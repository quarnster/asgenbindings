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
funcname = "RegisterMyTypes"
doassert = True
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
    elif sys.argv[i] == "-noassert":
        doassert = False
    elif sys.argv[i] == "-f":
        i += 1
        funcname = sys.argv[i]
    else:
        clang_args.append(sys.argv[i])
    i += 1

if output_filename == None:
    print """usage: %s -o <output-filename> <options to use with clang>
      -o        <filename> Specify which file to save output to"
      -v                   Enable verbose warning output
      -fir      <pattern>  File Inclusion Regex. Only cursors coming from file names matching the regex pattern will be added.
      -fer      <pattern>  File Exclusion regex. Cursors for which the filename matches the regex pattern will be excluded.
      -noassert            Don't do the assert check when registering
      -f        <name>     Name of the generated function

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

def get_type(type):
    pointer = type.kind == cindex.TypeKind.POINTER
    typename = ""
    ref = type.kind == cindex.TypeKind.LVALUEREFERENCE
    if type.kind == cindex.TypeKind.TYPEDEF or type.kind == cindex.TypeKind.RECORD:
        typename = type.get_declaration().spelling
    elif pointer or ref:
        typename = type.get_pointee().get_declaration().spelling
    else:
        typename = type.kind.name.lower()
    if typename == None:
        raise Exception("Typename was None")

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
    if ptr:
        name = name[:-1]
    while name in typedef:
        name = typedef[name]

    if ptr:
        return name + "*"
    return name

def get_as_type(name):
    name = name.replace("*", "@")
    if name == "char@" or name == "unsigned char@":
        return "string"
    return name


class Function:
    def __init__(self, cursor, clazz=None):
        args = []
        for child in cursor.get_children():
            if child.kind == cindex.CursorKind.PARM_DECL:
                typename = get_real_type(get_type(child.type))
                args.append(typename)
                add_use(typename)

        restype = get_real_type(get_type(cursor.result_type))
        add_use(restype)
        self.name = cursor.spelling
        self.args = args
        self.return_type = restype
        self.clazz = clazz

    def uses(self, typename):
        return self.return_type == typename or typename in self.args

    def pretty_name(self):
        cargs =  ", ".join(self.args)
        if self.clazz:
            return "%s %s::%s(%s)" % (self.return_type, self.clazz, self.name, cargs)
        else:
            return "%s %s(%s)" % (self.return_type, self.name, cargs)

    def get_register_string(self):
        asargs = ", ".join([get_as_type(at) for at in self.args])
        cargs =  ", ".join(self.args)
        if self.clazz == None:
            return _assert("engine->RegisterGlobalFunction(\"%s %s(%s)\", asFUNCTIONPR(%s, (%s), %s), asCALL_CDECL);" %
                        (get_as_type(self.return_type), self.name, self.args,
                         self.name, cargs, self.return_type))
        else:
            return _assert("engine->RegisterObjectMethod(\"%s\", \"%s %s(%s)\", asMETHODPR(%s, %s, (%s), %s), asCALL_THISCALL);" %
                (self.clazz, get_as_type(self.return_type), self.name, asargs, self.clazz, self.name, cargs, self.return_type))


class ObjectType:
    def __init__(self, name):
        self.name = name
        self.flags = {"asOBJ_APP_CLASS": True}

    def get_register_string(self):
        value_type = True
        if self.name in objecttype_scoreboard:
            score = objecttype_scoreboard[self.name]
            value_type = score[0] < score[1]
        else:
            warn("Warning: No uses of object type \"%s\" found. Guessing %s type." % (self.name, "value" if value_type else "reference"))
        if value_type:
            f = "|".join(self.flags)
            f = "asOBJ_VALUE|%s" % f
            return _assert("engine->RegisterObjectType(\"%s\", sizeof(%s), %s);" % (self.name, self.name, f))
        else:
            return _assert("engine->RegisterObjectType(\"%s\", 0, asOBJ_REF);" % (self.name))

class ObjectField:
    def __init__(self, clazz, name, type):
        self.clazz = clazz
        self.name = name
        self.type = type

    def uses(self, typename):
        return self.type == typename

    def pretty_name(self):
        return "%s %s::%s" % (self.type, self.clazz, self.name)

    def get_register_string(self):
        return _assert("engine->RegisterObjectProperty(\"%s\", \"%s %s\", asOFFSET(%s,%s));" % (self.clazz, self.type, self.name, self.clazz, self.name))


typedefs      = []
enums         = []
objecttypes   = []
functions     = []
objectmethods = []
objectfields  = []


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
                functions.append(Function(child))
            except Exception as e:
                warn("Warning: skipping function %s - %s" % (child.spelling, e))
        elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
            name, kind = get_typedef(child)
            if name:
                typedef[name] = kind
                typedefs.append(_assert("engine->RegisterTypedef(\"%s\", \"%s\");" % (name, get_real_type(kind))))
            else:
                warn("Warning, typedef too complex, skipping: %s" % name)
        elif child.kind == cindex.CursorKind.CLASS_DECL or child.kind == cindex.CursorKind.STRUCT_DECL:
            children = child.get_children()
            if len(children) == 0:
                continue

            idx = cindex.CXXAccessSpecifier.PRIVATE if child.kind == cindex.CursorKind.CLASS_DECL else cindex.CXXAccessSpecifier.PUBLIC
            access = cindex._cxx_access_specifiers[cindex.CXXAccessSpecifier.PRIVATE]
            classname = child.spelling
            o = ObjectType(classname)
            for child in children:
                if child.kind == cindex.CursorKind.CXX_ACCESS_SPEC_DECL:
                    access = child.get_cxx_access_specifier()
                    continue
                if not access.is_public():
                    continue
                if child.kind == cindex.CursorKind.CXX_METHOD:
                    if child.spelling == "operator=":
                        o.flags["asOBJ_APP_CLASS_ASSIGNMENT"] = True
                    try:
                        objectmethods.append(Function(child, classname))
                    except Exception as e:
                        warn("Warning: skipping member method %s::%s - %s" % (classname, child.spelling, e))
                elif child.kind == cindex.CursorKind.CONSTRUCTOR:
                    o.flags["asOBJ_APP_CLASS_CONSTRUCTOR"] = True
                elif child.kind == cindex.CursorKind.DESTRUCTOR:
                    o.flags["asOBJ_APP_CLASS_DESTRUCTOR"] = True
                elif child.kind == cindex.CursorKind.FIELD_DECL:
                    try:
                        type = get_real_type(get_type(child.type))
                        add_use(type)
                        objectfields.append(ObjectField(classname, child.spelling, type))
                    except Exception as e:
                        warn("Warning: skipping member field %s::%s - %s" % (classname, child.spelling, e))
                elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
                    name, kind = get_typedef(child)
                    if name:
                        typedef[name] = kind
                    warn("Typedefs within classes is not supported by AngelScript")
                else:
                    warn("Warning, unhandled cursor: %s, %s" % (child.displayname, child.kind))
            objecttypes.append(o)
        elif child.kind == cindex.CursorKind.MACRO_INSTANTIATION or \
                child.kind == cindex.CursorKind.CONVERSION_FUNCTION or \
                 child.kind == cindex.CursorKind.INCLUSION_DIRECTIVE or \
                 child.kind == cindex.CursorKind.UNEXPOSED_DECL:
            continue
        else:
            warn("Warning, unhandled cursor: %s, %s" % (child.displayname, child.kind))



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
        warn("Warning \"%s\" is used both as a reference type (%d) and a value type (%d). The following will be removed:" % (key, ref, val))
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

walk(tu.cursor)

# File processed, do some post processing
remove_ref_val_mismatches()


f = open(output_filename, "w")
f.write("#include <angelscript.h>\n\n")
f.write("void %s(asIScriptEngine* engine)\n{\n\t" % funcname)
f.write("\n\t".join(typedefs))
f.write("\n\t")
f.write("\n\t".join(enums))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in objecttypes]))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in functions]))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in objectmethods]))
f.write("\n\t")
f.write("\n\t".join([o.get_register_string() for o in objectfields]))
f.write("\n}\n")
f.close()

for diag in tu.diagnostics:
    warn("Warning, clang had the following to say: %s" % (diag.spelling))

print "Finished with %d warnings" % warn_count
