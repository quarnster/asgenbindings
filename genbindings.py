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

index = cindex.Index.create()

tu = index.parse(None, sys.argv[1:], [], 13)


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

    return "%s%s" % (typename, "@" if pointer else "&" if ref else "")

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
    if "@" in typename:
        p = 1
        typename = typename[:-1]

    if typename in objecttype_scoreboard:
        val = objecttype_scoreboard[typename]
    objecttype_scoreboard[typename] = (val[0]+p, val[1]+1-p)

typedef = {}

def get_real_type(name):
    ptr = "@" in name
    if ptr:
        name = name[:-1]
    while name in typedef:
        name = typedef[name]

    if ptr:
        return name + "@"
    return name

def get_as_type(name):
    if name == "char@" or name == "unsigned char@":
        return "string"
    return name


def get_function_def(cursor):
    args = ""
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.PARM_DECL:
            if len(args):
                args += ", "
            typename = get_real_type(get_type(child.type))
            args += typename
            add_use(typename)

    restype = get_real_type(get_type(cursor.result_type))
    add_use(restype)
    return (restype, cursor.spelling, args)


def _assert(line):
    return "r = %-128ls assert(r >= asSUCCESS);\n" % line


typedefs      = ""
enums         = ""
objecttypes   = ""
functions     = ""
objectmembers = ""


def walk(cursor):
    global typedefs
    global enums
    global objecttypes
    global functions
    global objectmembers
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.MACRO_DEFINITION:
            tokens = cindex.tokenize(tu, child.extent)
            if tokens[0].kind == cindex.TokenKind.IDENTIFIER and tokens[1].kind == cindex.TokenKind.LITERAL and is_int(tokens[1].spelling):
                enums += _assert("engine->RegisterEnumValue(\"HASH_DEFINES\", \"%s\", %s);" % (tokens[0].spelling, tokens[1].spelling))
        elif child.kind == cindex.CursorKind.FUNCTION_DECL:
            try:
                decl = get_function_def(child)
                functions += _assert("engine->RegisterGlobalFunction(\"%s %s(%s)\", asFUNCTIONPR(%s, (%s), %s), asCALL_CDECL);" % (decl[0], decl[1], decl[2], decl[1], decl[2].replace("@", "*"), decl[0]))
            except Exception as e:
                print "Warning: skipping function %s - %s" % (child.spelling, e)
        elif child.kind == cindex.CursorKind.TYPEDEF_DECL:
            tokens = cindex.tokenize(tu, child.extent)
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
                typedef[name] = kind
                typedefs += _assert("engine->RegisterTypedef(\"%s\", \"%s\");" % (name, get_real_type(kind)))
            else:
                data = ""
                for token in tokens:
                    data += token.spelling + " "
                print "Warning, typedef too complex, skipping: %s" % data
        elif child.kind == cindex.CursorKind.CLASS_DECL:
            children = child.get_children()
            if len(children) == 0:
                continue
            access = cindex._cxx_access_specifiers[cindex.CXXAccessSpecifier.PRIVATE]
            classname = child.spelling
            data = ""
            flags = {"asOBJ_APP_CLASS": True}
            for child in children:
                if child.kind == cindex.CursorKind.CXX_ACCESS_SPEC_DECL:
                    access = child.get_cxx_access_specifier()
                    continue
                if not access.is_public():
                    continue
                if child.kind == cindex.CursorKind.CXX_METHOD:
                    if child.spelling == "operator=":
                        flags["asOBJ_APP_CLASS_ASSIGNMENT"] = True
                    try:
                        decl = get_function_def(child)
                        objectmembers += _assert("engine->RegisterObjectMethod(\"%s\", \"%s %s(%s)\", asMETHODPR(%s, %s, (%s), %s), asCALL_THISCALL);" % (classname, decl[0], decl[1], decl[2], classname, decl[1], decl[2].replace("@", "*"), decl[0]))
                    except Exception as e:
                        print "Warning: skipping member method %s::%s - %s" % (classname, child.spelling, e)
                elif child.kind == cindex.CursorKind.CONSTRUCTOR:
                    flags["asOBJ_APP_CLASS_CONSTRUCTOR"] = True
                elif child.kind == cindex.CursorKind.DESTRUCTOR:
                    flags["asOBJ_APP_CLASS_DESTRUCTOR"] = True
            finalflags = "todo1"
            finalsize = "todo2"
            objecttypes += _assert("engine->RegisterObjectType(\"%s\", %s, %s);" % (classname, finalflags, finalsize))
        else:
            pass
            #sys.stderr.write("Warning, unhandled cursor: %s, %s\n" % (child.displayname, child.kind))


walk(tu.cursor)

# File processed, do some post processing
for key in objecttype_scoreboard:
    ref, val = objecttype_scoreboard[key]
    if ref == 0 or val == 0:
        continue
    print "Warning \"%s\" is used both as a reference type (%d) and a value type (%d). The following will be removed:" % (key, ref, val)
    regex = r"(\"|,\s|\(|$)%s%s(\)|,)" % (re.escape(key), "@" if val > ref else "")
    regex = re.compile(regex)

    innerre = re.compile(r"\"((.+\s)?([\w@]+\s+\w+\([^\)]*\)))\"")
    toadd = functions.split("\n")[:-1]
    functions = []
    while len(toadd):
        line = toadd.pop(0)
        if regex.search(line):
            print "\t%s" % innerre.search(line).group(1)
        else:
            functions.append(line)
    functions = "\n".join(functions)

    innerre = re.compile(r"\"(\w+)\", \"((.+\s)?[\w@]+)\s+(\w+\([^\)]*\))\"")
    toadd = objectmembers.split("\n")[:-1]
    objectmembers = []
    while len(toadd):
        line = toadd.pop(0)
        if regex.search(line):
            inner = innerre.search(line)
            print "\t%s %s::%s" % (inner.group(2), inner.group(1), inner.group(4))
        else:
            objectmembers.append(line)
    objectmembers = "\n".join(objectmembers)
    #if ref > val:
    #    re.compile(r"^.*(\s|\()%s(\s|,|\)$)"


f = open("generated.cpp", "w")
f.write(typedefs)
f.write(enums)
f.write(objecttypes)
f.write(functions)
f.write(objectmembers)
f.close()

for diag in tu.diagnostics:
    print "Warning, clang had the following to say: %s" % (diag.spelling)
