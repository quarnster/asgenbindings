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


output_filename = None
verbose = False
fir = None
fer = None
mir = None
mer = None
funcname = "RegisterMyTypes"
doassert = True
keep_unknowns = False
i = 1
clang_args = []
while i < len(sys.argv):
    if sys.argv[i] == "-o":
        i += 1
        output_filename = sys.argv[i]
    elif sys.argv[i] == "-v":
        verbose = True
    elif sys.argv[i] == "-fir":
        i += 1
        fir = re.compile(sys.argv[i])
    elif sys.argv[i] == "-fer":
        i += 1
        fer = re.compile(sys.argv[i])
    elif sys.argv[i] == "-mir":
        i += 1
        mir = re.compile(sys.argv[i])
    elif sys.argv[i] == "-mer":
        i += 1
        mer = re.compile(sys.argv[i])
    elif sys.argv[i] == "-noassert":
        doassert = False
    elif sys.argv[i] == "-f":
        i += 1
        funcname = sys.argv[i]
    elif sys.argv[i] == "-ku":
        keep_unknowns = True
    else:
        clang_args.append(sys.argv[i])
    i += 1

if output_filename == None:
    print """usage: %s -o <output-filename> <options to use with clang>
      -o        <filename> Specify which file to save output to"
      -v                   Enable verbose warning output
      -fir      <pattern>  File Inclusion Regex. Only cursors coming from file names matching the regex pattern will be added.
      -fer      <pattern>  File Exclusion regex. Cursors for which the filename matches the regex pattern will be excluded.
      -mir      <pattern>  Method/function Inclusion Regex. Only methods/functions matching the regex pattern will be added.
      -mer      <pattern>  Method/function Exclusion regex. Methods/functions that match the regex pattern will be excluded.
      -noassert            Don't do the assert check when registering
      -f        <name>     Name of the generated function
      -ku                  Keep functions and members declared with an unknown type. Useful if that type is registered elsewhere.

    Any unknown parameters will be forwarded to clang""" % (sys.argv[0])
    sys.exit(1)

index = cindex.Index.create()

tu = index.parse(None, clang_args, [], 13)


warn_count = 0
def warn(msg):
    global warn_count
    warn_count += 1
    if verbose:
        print msg

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


class Function:
    def __init__(self, cursor, clazz=None):
        self.args = []
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

        if self.clazz:
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
        namedict = {
            "-operator":       "opNeg",
            "~operator":       "opCom",
            "++operator":      "opPreInc",
            "--operator":      "opPreDec",
            "operator==":      "opEquals",
            "operator!=":      "opEquals",
            "operator<":       "opCmp",
            "operator<=":      "opCmp",
            "operator>":       "opCmp",
            "operator>=":      "opCmp",
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
        name = self.name
        if "operator" in name:
            if name not in namedict:
                raise Exception("Operator not supported in AngelScript %s" % self.pretty_name())
            name = namedict[name]
        asargs = []
        for a in self.args:
            asname = a.get_as_type()
            ref = "&" in asname
            if ref:
                asname2 = get_as_type(a.resolved)[:-1]
                extra = ""
                if asname2 in objecttype_scoreboard:
                    score = objecttype_scoreboard[asname2]
                    if score[1] >= score[0]:
                        # Value types can only be in or out references. Defaulting to in
                        asname += "in"
            asargs.append(asname)
        asargs = ", ".join(asargs)

        name = "%s %s(%s)" % (self.return_type.get_as_type(), name, asargs)
        if self.clazz and self.const:
            name += " const"

        return name

    def get_register_string(self):

        cargs =  ", ".join([at.get_c_type()  for at in self.args])
        if self.clazz == None:
            return _assert("engine->RegisterGlobalFunction(\"%s\", asFUNCTIONPR(%s, (%s), %s), asCALL_CDECL);" %
                        (self.asname(), self.name, cargs, self.return_type.get_c_type()))
        else:
            const = " const" if self.const else ""
            return _assert("engine->RegisterObjectMethod(\"%s\", \"%s\", asMETHODPR(%s, %s, (%s)%s, %s), asCALL_THISCALL);" %
                (self.clazz, self.asname(), self.clazz, self.name, cargs, const, self.return_type.get_c_type()))


class ObjectType:
    def add_fields(self, children, array):
        for child in children:
            if child.kind == cindex.CursorKind.CXX_BASE_SPECIFIER:
                self.add_fields(child.get_reference().get_children(), array)
            if child.kind == cindex.CursorKind.FIELD_DECL:
                array.append(child)

    def __init__(self, cursor, children, name):
        self.cursor = cursor
        self.name = name
        self.flags = {"asOBJ_APP_CLASS": True}
        fields = []

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
        value_type = True
        if self.name in objecttype_scoreboard:
            score = objecttype_scoreboard[self.name]
            value_type = score[0] < score[1]
        else:
            warn("No uses of object type \"%s\" found. Guessing %s type." % (self.name, "value" if value_type else "reference"))
        if value_type:
            f = "|".join(self.flags)
            f = "asOBJ_VALUE|%s" % f
            return _assert("engine->RegisterObjectType(\"%s\", sizeof(%s), %s);" % (self.name, self.name, f))
        else:
            ret = _assert("engine->RegisterObjectType(\"%s\", 0, asOBJ_REF);" % (self.name)) + \
            "\n\t" + _assert("engine->RegisterObjectBehaviour(\"%s\", asBEHAVE_ADDREF,  \"void f()\", asMETHOD(%s,AddRef), asCALL_THISCALL); assert( r >= 0 );" % (self.name, self.name)) + \
            "\n\t" + _assert("engine->RegisterObjectBehaviour(\"%s\", asBEHAVE_RELEASE, \"void f()\", asMETHOD(%s,DelRef), asCALL_THISCALL); assert( r >= 0 );" % (self.name, self.name))
            return ret




class ObjectField:
    def __init__(self, clazz, name, type):
        self.clazz = clazz
        self.name = name
        self.type = type

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

            idx = cindex.CXXAccessSpecifier.PRIVATE if child.kind == cindex.CursorKind.CLASS_DECL else cindex.CXXAccessSpecifier.PUBLIC
            access = cindex._cxx_access_specifiers[cindex.CXXAccessSpecifier.PRIVATE]
            classname = child.spelling
            if len(classname) == 0:
                classname = child.displayname
                if len(classname) == 0:
                    warn("Skipping class or struct defined at %s" % cursor.extent)
                    continue
            if classname in objecttypes:
                # TODO: different namespaces
                warn("Skipping type %s, as it is already defined" % classname)

            o = ObjectType(cursor, children, classname)
            for child in children:
                if child.kind == cindex.CursorKind.CXX_ACCESS_SPEC_DECL:
                    access = child.get_cxx_access_specifier()
                    continue
                if not access.is_public():
                    continue
                if child.kind == cindex.CursorKind.CXX_METHOD:
                    if child.spelling == "operator=":
                        o.flags["asOBJ_APP_CLASS_ASSIGNMENT"] = True
                    if child.get_cxxmethod_is_static():
                        warn("Skipping member method %s::%s as it's static" % (classname, child.spelling))
                        continue
                    try:
                        objectmethods.append(Function(child, classname))
                    except Exception as e:
                        warn("Skipping member method %s::%s - %s" % (classname, child.spelling, e))
                elif child.kind == cindex.CursorKind.CONSTRUCTOR:
                    o.flags["asOBJ_APP_CLASS_CONSTRUCTOR"] = True
                elif child.kind == cindex.CursorKind.DESTRUCTOR:
                    o.flags["asOBJ_APP_CLASS_DESTRUCTOR"] = True
                elif child.kind == cindex.CursorKind.FIELD_DECL:
                    try:
                        type = Type(child.type)
                        objectfields.append(ObjectField(classname, child.spelling, type))
                    except Exception as e:
                        warn("Skipping member field %s::%s - %s" % (classname, child.spelling, e))
                elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
                    name, kind = get_typedef(child)
                    if name:
                        typedef[name] = kind
                    warn("Typedefs within classes is not supported by AngelScript")
                else:
                    warn("Unhandled cursor: %s, %s" % (child.displayname, child.kind))
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
def remove_ref_val_mismatches():
    global typedefs
    global enums
    global objecttypes
    global functions
    global objectmethods
    for key in objecttype_scoreboard:
        ref, val = objecttype_scoreboard[key]
        if ref == 0 or val == 0:
            continue
        warn("\"%s\" is used both as a reference type (%d) and a value type (%d). The following will be removed:" % (key, ref, val))
        toremove = "%s%s" % (key, "*" if val > ref else "")

        toadd = functions
        functions = []
        while len(toadd):
            curr = toadd.pop(0)
            if curr.uses(toremove):
                warn("\t%s" % curr.pretty_name())
            else:
                functions.append(curr)

        toadd = objectmethods
        objectmethods = []
        while len(toadd):
            curr = toadd.pop(0)
            if curr.uses(toremove):
                warn("\t%s" % curr.pretty_name())
            else:
                objectmethods.append(curr)

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
    global typedefs
    global enums
    global objecttypes
    global functions
    global objectmethods

    functions = unknown_filter(functions)
    objectmethods = unknown_filter(objectmethods)

walk(tu.cursor)

# File processed, do some post processing
remove_ref_val_mismatches()

if not keep_unknowns:
    remove_unknowns()


f = open(output_filename, "w")
f.write("#include <angelscript.h>\n#include <assert.h>\n\n")
if len(includes):
    f.write("#include \"")
    f.write("\"\n#include \"".join(includes))
    f.write("\"")

f.write("\n\n")
f.write("void %s(asIScriptEngine* engine)\n{\n\tint r;\n\n\t" % funcname)

f.write("\n\t".join([objecttypes[o].get_register_string() for o in objecttypes]))
f.write("\n\t")
f.write("\n\t".join(typedefs))
f.write("\n\t")
f.write("\n\t".join(enums))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in functions]))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in objectmethods]))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in objectfields]))
f.write("\n}\n")
f.close()

for diag in tu.diagnostics:
    warn("clang had the following to say: %s" % (diag.spelling))

print "Finished with %d warnings" % warn_count
