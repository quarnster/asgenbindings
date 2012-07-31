# Copyright (c) 2012 Fredrik Ehnbom
#
# This software is provided 'as-is', without any express or implied
# warranty. In no event will the authors be held liable for any damages
# arising from the use of this software.
#
# Permission is granted to anyone to use this software for any purpose,
# including commercial applications, and to alter it and redistribute it
# freely, subject to the following restrictions:
#
#    1. The origin of this software must not be misrepresented; you must not
#    claim that you wrote the original software. If you use this software
#    in a product, an acknowledgment in the product documentation would be
#    appreciated but is not required.
#
#    2. Altered source versions must be plainly marked as such, and must not be
#    misrepresented as being the original software.
#
#    3. This notice may not be removed or altered from any source
#    distribution.
from clang import cindex
import sys
import re
import json
import os.path
import copy

i = 1

if len(sys.argv) != 2:
    print "usage: %s configfile.json"
    sys.exit(1)


f = open(sys.argv[1])
config = json.load(f)
f.close()


def get(name, default=None, conf=config):
    if name in conf:
        return conf[name]
    else:
        return default

fir = get("file_include_regex", None)
fer = get("file_exclude_regex", None)
mir = get("method_include_regex", None)
mer = get("method_exclude_regex", None)
oir = get("object_include_regex", None)
oer = get("object_exclude_regex", None)
mfir = get("field_include_regex", None)
mfer = get("field_exclude_regex", None)
generic_regex = get("generic_wrapper_regex", None)

fir = re.compile(fir) if fir else fir
fer = re.compile(fer) if fer else fer
mir = re.compile(mir) if mir else mir
mer = re.compile(mer) if mer else mer
oir = re.compile(oir) if oir else oir
oer = re.compile(oer) if oer else oer
mfir = re.compile(mfir) if mfir else mfir
mfer = re.compile(mfer) if mfer else mfer
generic_regex = re.compile(generic_regex) if generic_regex else generic_regex

verbose = get("verbose", False)
doassert = get("assert", True)
keep_unknowns = get("keep_unknowns", False)
output_filename = get("output_filename", None)
funcname = get("function_name", "RegisterMyTypes")

generic_wrappers = []

index = cindex.Index.create()

clang_args = get("clang_args", [])
clang_args.insert(0, "-I%s/clang/include" % os.path.dirname(os.path.abspath(__file__)))
tu = index.parse(None, clang_args, [], 13)


warn_count = 0
def warn(msg):
    global warn_count
    warn_count += 1
    if verbose:
        sys.stderr.write(msg + "\n")

def get_type(type, cursor=None):
    pointer = type.kind == cindex.TypeKind.POINTER
    typename = ""
    ref = type.kind == cindex.TypeKind.LVALUEREFERENCE
    if type.kind == cindex.TypeKind.TYPEDEF or type.kind == cindex.TypeKind.RECORD or type.kind == cindex.TypeKind.ENUM:
        typename = type.get_declaration()
    elif pointer or ref:
        typename = type.get_pointee().get_declaration()
    elif type.kind == cindex.TypeKind.ULONG:
        typename = "unsigned long"
    elif type.kind == cindex.TypeKind.UINT:
        typename = "unsigned int"
    elif type.kind == cindex.TypeKind.USHORT:
        typename = "unsigned short"
    elif type.kind == cindex.TypeKind.CONSTANTARRAY:
        if cursor is None:
            raise Exception("Constant array, but cursor not provided so can't solve the type")

        typename = get_type(type.get_array_element_type())
    else:
        typename = type.kind.name.lower()
    if typename is None:
        raise Exception("Typename was None")
    elif isinstance(typename, cindex.Cursor):
        if typename.spelling == None:
            raise Exception("Typename was None")

        fullname = [typename.spelling]
        cursor = typename.get_lexical_parent()
        while not cursor is None and (cursor.kind == cindex.CursorKind.NAMESPACE or cursor.kind == cindex.CursorKind.CLASS_DECL):
            fullname.insert(0, cursor.displayname)
            cursor = cursor.get_lexical_parent()
        typename = "::".join(fullname)
    elif typename == "unexposed":
        raise Exception("Typename is unexposed")

    return "%s%s" % (typename, "*" if pointer else "&" if ref else "")

def is_int(literal):
    try:
        i = int(literal)
        return True

    except:
        try:
            i = int(literal, 16)
            return True
        except:
            pass
        return False

objecttype_scoreboard = {}

def add_use(typename):
    val = (0, 0)
    p = 0
    if "*" in typename:
        p = 1
        typename = typename[:-1]

    if typename in objecttype_scoreboard:
        val = objecttype_scoreboard[typename]
    objecttype_scoreboard[typename] = (val[0]+p, val[1]+1-p)

typedef = {}

def get_real_type(name):
    ptr = "*" in name
    ref = "&" in name
    if ptr or ref:
        name = name[:-1]
    while name in typedef:
        name = typedef[name]

    if ptr:
        return name + "*"
    if ref:
        return name + "&"
    return name


def is_const(cursor):
    tokens = cindex.tokenize(tu, cursor.extent)
    for token in tokens:
        if token.spelling == "const":
            return True
    return False

as_builtins = {
    "unsigned long": "uint64",
    "unsigned int": "uint",
    "unsigned short": "uint16",
    "unsigned char": "uint8",
    "long": "int64",
    "void": "void",
    "double": "double",
    "float": "float",
    "char": "int8",
    "short": "int16",
    "int": "int",
    "long": "int64",
    "bool": "bool"
    }
def get_as_type(name):
    ptr = "*" in name
    ref = "&" in name
    name = name.replace("*", "").replace("&", "")

    if name in as_builtins:
        if ptr:
            raise Exception("Built-in value type %s used as a reference type" % (as_builtins[name]))
        name = as_builtins[name]
    return "%s%s%s" % (name, "@" if ptr else "", "&" if ref else "")

class Type:
    def __init__(self, kind):
        typename = get_type(kind)
        self.cname = typename
        typename = get_real_type(typename)
        self.resolved = typename
        add_use(typename)
        self.const = kind.is_const_qualified()
        get_as_type(self.resolved)

    def __repr__(self):
        return self.cname

    def get_as_type(self):
        return "%s%s" % ("const " if self.const else "", get_as_type(self.resolved))

    def get_c_type(self):
        return "%s%s" % ("const " if self.const else "", self.cname)


def is_reference_type(name):
    if name in config["object_types"] and "reference" in config["object_types"][name]:
        return config["object_types"][name]["reference"]
    elif name in objecttypes:
        ot = objecttypes[name]
        for p in ot.parents:
            v = is_reference_type(p)
            if not v is None:
                return v
    if name in objecttype_scoreboard:
        score = objecttype_scoreboard[name]
        return score[0] > score[1]
    return None


operatornamedict = {
    "-operator":       "opNeg",
    "~operator":       "opCom",
    "++operator":      "opPreInc",
    "--operator":      "opPreDec",
    "operator==":      "opEquals",
    #"operator!=":      "opEquals",
    "operator<":       "opCmp",
    # "operator<=":      "opCmp",
    # "operator>":       "opCmp",
    # "operator>=":      "opCmp",
    "operator++":      "opPostInc",
    "operator--":      "opPostDec",
    "operator+":       "opAdd",
    "operator-":       "opSub",
    "operator*":       "opMul",
    "operator/":       "opDiv",
    "operator%":       "opMod",
    "operator&":       "opAnd",
    "operator|":       "opOr",
    "operator^":       "opXor",
    "operator<<":      "opShl",
    "operator>>":      "opShr",
    "operator>>>":     "opUShr",
    "operator[]":      "opIndex",
    "operator=":       "opAssign",
    "operator+=":      "opAddAssign",
    "operator-=":      "opSubAssign",
    "operator*=":      "opMulAssign",
    "operator/=":      "opDivAssign",
    "operator%=":      "opModAssign",
    "operator&=":      "opAndAssign",
    "operator|=":      "opOrAssign",
    "operator^=":      "opXorAssign",
    "operator<<=":     "opShlAssign",
    "operator>>=":     "opShrAssign",
    "operator>>>=":    "opUShrAssign",
}
class Function(object):
    def __init__(self, cursor, clazz=None, behaviour=None):
        self.args = []
        if cursor is None:
            return

        children = cursor.get_children()
        for child in children:
            if child.kind == cindex.CursorKind.PARM_DECL:
                t = Type(child.type)
                t.const = is_const(child)
                self.args.append(t)

        self.name = cursor.spelling
        self.return_type = Type(cursor.result_type)
        self.clazz = clazz
        self.const = False
        self.behaviour = behaviour

        if self.clazz and not behaviour:
            start = cursor.extent.start
            end = cursor.extent.end
            i = 0
            while i < len(children):
                if children[i].kind == cindex.CursorKind.PARM_DECL:
                    start = children[i].extent.end
                if children[i].kind == cindex.CursorKind.COMPOUND_STMT:
                    if i > 0:
                        start = children[i-1].extent.end
                    end = children[i].extent.start
                    break
                i += 1
                if i == len(children):
                    break
                start = children[i-1].extent.end


            r = cindex.SourceRange.from_locations(start, end)
            f = open(cursor.location.file.name)
            f.seek(start.offset)
            length = end.offset-start.offset
            data = f.read(length)
            f.close()
            self.const = re.search(r"\s*const\s*(=\s*0)?$", data) != None

            if len(children) > 0 and children[0].kind != cindex.CursorKind.PARM_DECL:
                f = open(cursor.location.file.name)
                f.seek(cursor.extent.start.offset)
                length = children[0].extent.start.offset-cursor.extent.start.offset
                data = f.read(length)
                f.close()
                data = re.sub(r"%s.*" % self.name, "", data)
                self.return_type.const = re.search(r"\s*const\s*$", data) != None
        self.asname()
        if mir or mer:
            pn = self.pretty_name()
            if mer and mer.search(pn):
                raise Exception("Function matches exclusion pattern. %s" % pn)
            if mir and not mir.search(pn):
                raise Exception("Function does not match inclusion pattern. %s" % pn)

    def uses(self, typename):
        if self.return_type.resolved == typename:
            return True
        for t in self.args:
            if t.resolved == typename:
                return True
        return False

    def pretty_name(self):
        cargs =  ", ".join([t.get_c_type() for t in self.args])
        if self.clazz:
            return "%s %s::%s(%s)" % (self.return_type, self.clazz, self.name, cargs)
        else:
            return "%s %s(%s)" % (self.return_type, self.name, cargs)

    def asname(self):

        name = self.name
        if "operator" in name:
            if name not in operatornamedict:
                raise Exception("Operator not supported in AngelScript %s" % self.pretty_name())
            name = operatornamedict[name]
        asargs = []
        for a in self.args:
            asname = a.get_as_type()
            ref = "&" in asname
            if ref:
                asname2 = get_as_type(a.resolved)[:-1]
                extra = ""

                if not is_reference_type(asname2):
                    # Value types can only be in or out references. Defaulting to in
                    asname += "in"
            asargs.append(asname)
        asargs = ", ".join(asargs)

        if self.behaviour == "asBEHAVE_CONSTRUCT" or self.behaviour == "asBEHAVE_FACTORY":
            name = "void f(%s)" % (asargs)

            if is_reference_type(self.clazz):
                name = "%s@ %s(%s)" % (self.clazz, self.clazz, asargs)
                self.behaviour = "asBEHAVE_FACTORY"
        elif self.behaviour == "asBEHAVE_DESTRUCT":
            name = "void f()"
        else:
            name = "%s %s(%s)" % (self.return_type.get_as_type(), name, asargs)
        if self.clazz and self.const:
            name += " const"

        return name

    def get_generic(self):
        lut = {
            "double": "Double",
            "float": "Float",
            "uint": "DWord",
            "int": "DWord",
            "uint16": "Word",
            "int16": "Word",
            "uint8": "Byte",
            "int8": "Byte",
            "bool": "Byte"
        }
        name = self.name
        if "operator" in name:
            name = operatornamedict[name]
        name = name.replace("~", "tilde") + "_generic"
        for arg in self.args:
            name += "_" + arg.get_c_type().replace("&", "amp").replace("*", "star").replace(" ", "space")
        if self.clazz:
            name = self.clazz + "_" + name
        func = "void %s(asIScriptGeneric *gen)\n{\n" % name
        asret = self.return_type.get_as_type()
        call = "%s(" % self.name
        if self.clazz:
            if is_reference_type(self.clazz) and self.behaviour == "asBEHAVE_CONSTRUCT":
                self.behaviour = "asBEHAVE_FACTORY"

            if self.behaviour == "asBEHAVE_FACTORY":
                call = "gen->SetReturnObject(new %s(" % (self.name)
            elif self.behaviour == "asBEHAVE_CONSTRUCT":
                call = "new(gen->GetObject()) %s(" % self.name
            else:
                call = "static_cast<%s*>(gen->GetObject())->%s" % (self.clazz, call)

        for i in range(len(self.args)):
            if i > 0:
                call += ", "
            arg = self.args[i]
            t = arg.get_as_type()
            if t in lut:
                call += "gen->GetArg%s(%d)" % (lut[t], i)
            else:
                ct = arg.get_c_type()
                pt = "*" in ct
                star = "*" if not pt else ""
                call += "%sstatic_cast<%s%s>(gen->GetArgAddress(%d))" % (star, arg.get_c_type().replace("&", ""), star, i)
        call += ")"
        if self.behaviour == "asBEHAVE_FACTORY":
            call += ")"

        asret2 = asret.replace("const ", "").strip()
        if asret2 in lut:
            func += "\tgen->SetReturn%s(%s);\n" % (lut[asret2], call)
        elif asret == "void":
            func += "\t" + call + ";\n"
        else:
            ct = self.return_type.get_c_type()
            pt = "*" in ct
            star = "*" if not pt else ""
            if pt:
                func += "\tgen->SetReturnObject(%s);\n" % (call)
            elif "&" in ct:
                func += "\tgen->SetReturnAddress((void*)&%s);\n" % (call)
            else:

                func += "\t" + self.return_type.get_c_type().replace("&", "").replace("const ", "") + " ret = %s;\n" % call
                func += "\tgen->SetReturnObject(&ret);\n"

                #func += "\t" + self.return_type.get_c_type() + " ret = %s;\n" % call
                #func += "\tnew(gen->GetAddressOfReturnLocation()) %s(ret);\n" % self.return_type.get_c_type().replace("&", "")
        func += "}\n"
        generic_wrappers.append(func)

        return "asFUNCTION(%s), asCALL_GENERIC" % (name)


    def get_register_string(self):
        global generic_wrappers
        cargs =  ", ".join([at.get_c_type()  for at in self.args])

        if self.clazz == None:
            callconv = "asCALL_CDECL"
            call = "asFUNCTIONPR(%s, (%s), %s), %s" % (self.name, cargs, self.return_type.get_c_type(), callconv)

            if generic_regex and generic_regex.search(self.pretty_name()):
                call = self.get_generic()
            return _assert("engine->RegisterGlobalFunction(\"%s\", %s);" % (self.asname(), call))
        else:
            const = " const" if self.const else ""
            call = "asMETHODPR(%s, %s, (%s)%s, %s), asCALL_THISCALL" % (self.clazz, self.name, cargs, const, self.return_type.get_c_type())
            if (generic_regex and generic_regex.search(self.pretty_name())) or \
                    self.behaviour == "asBEHAVE_CONSTRUCT" or \
                    self.behaviour == "asBEHAVE_DESTRUCT" or \
                    self.behaviour == "asBEHAVE_FACTORY":
                call = self.get_generic()
            if self.behaviour == None:
                return _assert("engine->RegisterObjectMethod(\"%s\", \"%s\", %s);" % (self.clazz, self.asname(), call))
            else:
                name = self.asname()
                return _assert("engine->RegisterObjectBehaviour(\"%s\", %s, \"%s\", %s);" % (self.clazz, self.behaviour, name, call))


objectindex = 0
class ObjectType:
    def add_fields(self, children, array):
        for child in children:
            if child.kind == cindex.CursorKind.CXX_BASE_SPECIFIER:
                self.add_fields(child.get_reference().get_children(), array)
            if child.kind == cindex.CursorKind.FIELD_DECL:
                array.append(child)

    def __init__(self, cursor, children, name):
        global objectindex
        self.cursor = cursor
        self.name = name
        self.flags = {"asOBJ_APP_CLASS": True}
        fields = []
        self.parents = []
        self.index = objectindex
        objectindex += 1

        idx = cindex.CXXAccessSpecifier.PRIVATE if cursor.kind == cindex.CursorKind.CLASS_DECL else cindex.CXXAccessSpecifier.PUBLIC
        access = cindex._cxx_access_specifiers[idx]
        for child in children:

            if child.kind == cindex.CursorKind.CXX_BASE_SPECIFIER:
                c = child.get_resolved_cursor()
                parentname = c.spelling
                self.parents.append(parentname)
                toadd = []
                for om in objectmethods:
                    if om.clazz == parentname:
                        f = copy.deepcopy(om)
                        f.clazz = self.name
                        toadd.append(f)
                objectmethods.extend(toadd)
                toadd = []
                for of in objectfields:
                    if of.clazz == parentname:
                        f = copy.deepcopy(of)
                        f.clazz = self.name
                        toadd.append(f)
                objectfields.extend(toadd)
                continue

            if child.kind == cindex.CursorKind.CXX_ACCESS_SPEC_DECL:
                access = child.get_cxx_access_specifier()
                continue
            if not access.is_public():
                continue

            elif child.kind == cindex.CursorKind.CXX_METHOD:
                if child.spelling == "operator=":
                    self.flags["asOBJ_APP_CLASS_ASSIGNMENT"] = True
                if child.get_cxxmethod_is_static():
                    # TODO
                    warn("Skipping member method %s::%s as it's static" % (self.name, child.spelling))
                    continue
                try:
                    objectmethods.append(Function(child, self.name))
                except Exception as e:
                    warn("Skipping member method %s::%s - %s" % (self.name, child.spelling, e))
            elif child.kind == cindex.CursorKind.CONSTRUCTOR:
                self.flags["asOBJ_APP_CLASS_CONSTRUCTOR"] = True
                try:
                    f = Function(child, self.name, "asBEHAVE_CONSTRUCT")
                    behaviours.append(f)
                except Exception as e:
                    warn("Skipping constructor %s::%s - %s" % (self.name, child.spelling, e))
            elif child.kind == cindex.CursorKind.DESTRUCTOR:
                self.flags["asOBJ_APP_CLASS_DESTRUCTOR"] = True
                try:
                    f = Function(child, self.name, "asBEHAVE_DESTRUCT")
                    behaviours.append(f)
                except Exception as e:
                    warn("Skipping destructor %s::%s - %s" % (self.name, child.spelling, e))
            elif child.kind == cindex.CursorKind.FIELD_DECL:
                try:
                    type = Type(child.type)
                    objectfields.append(ObjectField(self.name, child.spelling, type))
                except Exception as e:
                    warn("Skipping member field %s::%s - %s" % (self.name, child.spelling, e))
            elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
                name, kind = get_typedef(child)
                if name:
                    typedef[name] = kind
                warn("Typedefs within classes is not supported by AngelScript")
            else:
                warn("Unhandled cursor: %s, %s" % (child.displayname, child.kind))
        if "asOBJ_APP_CLASS_DESTRUCTOR" not in self.flags:
            self.flags["asOBJ_POD"] = True


        #self.add_fields(children, fields)
        #if len(fields):
        #    try:
        #        child = fields.pop(0)
        #        t = get_real_type(get_type(child.type, child))
        #        allEqual = True
        #        for field in fields:
        #            t2 = get_real_type(get_type(field.type, field))
        #            if t2 != t:
        #                break
        #        if allEqual:
        #            if t == "float":
        #                self.flags["asOBJ_APP_CLASS_ALLFLOATS"] = True
        #            elif t == "int" or t == "unsigned int":
        #                self.flags["asOBJ_APP_CLASS_ALLINTS"] = True
        #            print "%s has all fields of equal type: %s" % (self.name, t)
        #    except:
        #        pass


    def get_register_string(self):
        flags = [] if is_reference_type(self.name) else self.flags
        if self.name in config["object_types"]:
            conf = config["object_types"][self.name]
            if "flags" in conf:
                flags = conf["flags"]
            if "extra_flags" in conf:
                flags.extend(conf["extra_flags"])

        f = "%s%s%s" % ("asOBJ_REF" if is_reference_type(self.name) else "asOBJ_VALUE", "|" if len(flags) else "", "|".join(flags))
        if not is_reference_type(self.name):
            return _assert("engine->RegisterObjectType(\"%s\", sizeof(%s), %s);" % (self.name, self.name, f))

        ret = _assert("engine->RegisterObjectType(\"%s\", 0, %s);" % (self.name, f))
        for parent in self.parents:
            extra = "_nocount" if "asOBJ_NOCOUNT" in flags else ""
            ret += "\n\t" + _assert("engine->RegisterObjectBehaviour(\"%s\", asBEHAVE_REF_CAST, \"%s@ f()\", asFUNCTION((refCast%s<%s,%s>)), asCALL_CDECL_OBJLAST);" % (parent, self.name, extra,  parent, self.name))
            ret += "\n\t" + _assert("engine->RegisterObjectBehaviour(\"%s\", asBEHAVE_IMPLICIT_REF_CAST, \"%s@ f()\", asFUNCTION((refCast%s<%s,%s>)), asCALL_CDECL_OBJLAST);" % (self.name, parent, extra, self.name, parent))

        if not "asOBJ_NOCOUNT" in flags:
            f = Function(None)
            f.name = "AddRef"
            f.clazz = self.name
            f.const = False
            t = cindex.Type(cindex.TypeKind.VOID.from_param())
            f.behaviour = "asBEHAVE_ADDREF"
            f.return_type = Type(t)
            behaviours.append(f)

            f = copy.deepcopy(f)
            f.name = "DelRef"
            f.behaviour = "asBEHAVE_RELEASE"
            behaviours.append(f)
        return ret




class ObjectField:
    def __init__(self, clazz, name, type):
        self.clazz = clazz
        self.name = name
        self.type = type
        pn = self.pretty_name()
        if mfer and mfer.search(pn):
            raise Exception("Matches exclude pattern")
        if mfir and not mfir.search(pn):
            raise Exception("Doesn't match include pattern")

    def uses(self, typename):
        return self.type.resolved == typename

    def pretty_name(self):
        return "%s %s::%s" % (self.type, self.clazz, self.name)

    def get_register_string(self):
        return _assert("engine->RegisterObjectProperty(\"%s\", \"%s %s\", asOFFSET(%s,%s));" % (self.clazz, self.type, self.name, self.clazz, self.name))

typedefs      = []
enums         = []
objecttypes   = {}
functions     = []
objectmethods = []
objectfields  = []
includes      = []
behaviours     = []

def _assert(line):
    if doassert:
        return "r = %-128ls assert(r >= asSUCCESS);" % line
    else:
        return line


def get_typedef(cursor):
    tokens = cindex.tokenize(tu, cursor.extent)
    good = True
    if len(tokens) >= 4:
        for x in tokens[1:-2]:
            if x.kind != cindex.TokenKind.IDENTIFIER and x.kind != cindex.TokenKind.KEYWORD:
                good = False
                break
    else:
        good = False
    if good:
        kind = " ".join([t.spelling for t in tokens[1:len(tokens)-2]])
        name = tokens[len(tokens)-2].spelling
    else:
        data = ""
        for token in tokens:
            data += token.spelling + " "
        return None, data
    return name, kind

def add_include(filename):
    if not filename in includes and filename.endswith(".h"):
        includes.append(filename)

def walk(cursor):
    global typedefs
    global enums
    global objecttypes
    global functions
    global objectmethods
    for child in cursor.get_children():
        if not child.location.file:
            continue
        filename = child.location.file.name
        if child.kind == cindex.CursorKind.TYPEDEF_DECL:
            name, kind = get_typedef(child)
            if name:
                typedef[name] = kind

        if fer and fer.search(filename):
            continue
        if fir and not fir.search(filename):
            continue
        if child.kind == cindex.CursorKind.MACRO_DEFINITION:
            tokens = cindex.tokenize(tu, child.extent)
            if tokens[0].kind == cindex.TokenKind.IDENTIFIER and tokens[1].kind == cindex.TokenKind.LITERAL and is_int(tokens[1].spelling):
                enums.append(_assert("engine->RegisterEnumValue(\"HASH_DEFINES\", \"%s\", %s);" % (tokens[0].spelling, tokens[1].spelling)))
        elif child.kind == cindex.CursorKind.FUNCTION_DECL:
            try:
                f = Function(child)
                if "operator" in f.name:
                    raise Exception("Non member operator functions not supported currently")
                else:
                    functions.append(f)
                add_include(filename)
            except Exception as e:
                warn("Skipping function %s - %s" % (child.spelling, e))
        elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
            name, kind = get_typedef(child)
            if name:
                typedef[name] = kind
                if get_real_type(kind) not in as_builtins:
                    warn("Typedef %s = %s can't be registered as it doesn't resolve to an AngelScript builtin type" % (name, kind))
                else:
                    typedefs.append(_assert("engine->RegisterTypedef(\"%s\", \"%s\");" % (name, get_real_type(kind))))
            else:
                warn("Typedef too complex, skipping: %s" % name)
        elif child.kind == cindex.CursorKind.CLASS_DECL or child.kind == cindex.CursorKind.STRUCT_DECL:
            children = child.get_children()
            if len(children) == 0:
                continue

            if oer and oer.search(child.spelling):
                continue
            if oir and not oir.search(child.spelling):
                continue


            classname = child.spelling
            if len(classname) == 0:
                classname = child.displayname
                if len(classname) == 0:
                    warn("Skipping class or struct defined at %s" % cursor.extent)
                    continue
            if classname in objecttypes:
                # TODO: different namespaces
                warn("Skipping type %s, as it is already defined" % classname)

            o = ObjectType(child, children, classname)

            objecttypes[classname] = o
            add_include(filename)
        elif child.kind == cindex.CursorKind.MACRO_INSTANTIATION or \
                child.kind == cindex.CursorKind.CONVERSION_FUNCTION or \
                 child.kind == cindex.CursorKind.INCLUSION_DIRECTIVE or \
                 child.kind == cindex.CursorKind.UNEXPOSED_DECL:
            continue
        else:
            warn("Unhandled cursor: %s, %s" % (child.displayname, child.kind))



# Removes usage of object types that are used both as a reference and a value type
def mismatch_filter(source, toremove):
    toadd =source
    ret = []
    while len(toadd):
        curr = toadd.pop(0)
        if curr.uses(toremove):
            warn("\t%s" % curr.pretty_name())
        else:
            ret.append(curr)
    return ret

def remove_ref_val_mismatches():
    global functions
    global objectmethods
    global behaviours
    for key in objecttype_scoreboard:
        isref = is_reference_type(key)
        ref, val = objecttype_scoreboard[key]
        if (isref and val == 0) or (not isref and ref == 0):
            continue
        warn("\"%s\" is used both as a reference type (%d) and a value type (%d). The following will be removed:" % (key, ref, val))
        toremove = "%s%s" % (key, "*" if not isref else "")

        functions = mismatch_filter(functions, toremove)
        objectmethods = mismatch_filter(objectmethods, toremove)
        behaviours = mismatch_filter(behaviours, toremove)


def is_known(name):
    name = name.replace("*", "").replace("&", "")
    return name in objecttypes or name in as_builtins

def unknown_filter(source):
    toadd = source
    ret = []
    while len(toadd):
        keep = True
        curr = toadd.pop(0)
        broken = None
        for t in curr.args:
            if not is_known(t.resolved):
                broken = t.resolved
                keep = False
        if not is_known(curr.return_type.resolved):
            broken = curr.return_type.resolved
            keep = False
        if not keep:
            warn("Removing %s as it's using an unknown type %s [disable with -ku]" % (curr.pretty_name(), broken))
        else:
            ret.append(curr)
    return ret

def remove_unknowns():
    global functions
    global objectmethods
    global behaviours

    functions = unknown_filter(functions)
    objectmethods = unknown_filter(objectmethods)
    behaviours = unknown_filter(behaviours)


def dup_filter(source):
    toadd = source
    ret = []
    names = []
    while len(toadd):
        keep = True
        curr = toadd.pop(0)
        pn = curr.pretty_name()
        if pn in names:
            warn("Removing duplicate function %s" % pn)
        else:
            ret.append(curr)
            names.append(pn)
    return ret

def remove_duplicates():
    global functions
    global objectmethods
    global behaviours

    functions = dup_filter(functions)
    objectmethods = dup_filter(objectmethods)
    behaviours = dup_filter(behaviours)


def remove_reference_destructors():
    global behaviours
    toadd = behaviours
    behaviours = []
    while len(toadd):
        curr = toadd.pop(0)
        if is_reference_type(curr.clazz) and curr.behaviour == "asBEHAVE_DESTRUCT":
            warn("Removing destructor for reference type %s" % curr.clazz)
        else:
            behaviours.append(curr)

walk(tu.cursor)

# File processed, do some post processing
remove_ref_val_mismatches()

if not keep_unknowns:
    remove_unknowns()
remove_duplicates()
remove_reference_destructors()


f = sys.stdout
if output_filename != None:
    f = open(output_filename, "w")
f.write("#include <angelscript.h>\n#include <assert.h>\n\n")

if len(includes):
    f.write("#include \"")
    f.write("\"\n#include \"".join(includes))
    f.write("\"")

f.write("""
template<class A, class B>
B* refCast(A* a)
{
    if(!a) return NULL;

    B* b = dynamic_cast<B*>(a);
    if (b != NULL)
    {
        b->AddRef();
    }
    return b;
}
template<class A, class B>
B* refCast_nocount(A* a)
{
    if( !a ) return NULL;
    return dynamic_cast<B*>(a);
}
""")

data  = "void %s(asIScriptEngine* engine)\n{\n\tint r;\n\n\t" % funcname
ot = [objecttypes[o] for o in objecttypes]
ot.sort(cmp=lambda a, b:  cmp(a.index, b.index))
data += "\n\t".join([o.get_register_string() for o in ot])
data += "\n\t"
data += "\n\t".join(typedefs)
data += "\n\t"
data += "\n\t".join(enums)
data += "\n\t"
data += "\n\t".join([o.get_register_string() for o in functions])
data += "\n\t"
data += "\n\t".join([o.get_register_string() for o in behaviours])
data += "\n\t"
data += "\n\t".join([o.get_register_string() for o in objectmethods])
data += "\n\t"
data += "\n\t".join([o.get_register_string() for o in objectfields])
data += "\n}\n"

f.write("\n".join(generic_wrappers))
f.write("\n\n")

f.write(data)
if output_filename != None:
    f.close()

for diag in tu.diagnostics:
    warn("clang had the following to say: %s" % (diag.spelling))

sys.stderr.write("Finished with %d warnings\n" % warn_count)
