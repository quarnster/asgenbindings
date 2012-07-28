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

index = cindex.Index.create()

tu = index.parse(None, sys.argv[1:], [], 13)


def get_type(type):
    pointer = type.kind == cindex.TypeKind.POINTER
    typename = ""
    if type.kind == cindex.TypeKind.TYPEDEF:
        typename = type.get_declaration().spelling
    elif pointer:
        typename = type.get_pointee().get_declaration().spelling
    else:
        typename = type.kind.name.lower()

    return "%s%s" % (typename, "*" if pointer else "")

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


def get_function_def(cursor):
    args = ""
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.PARM_DECL:
            if len(args):
                args += ", "
            args += get_type(child.type)


    return (get_type(cursor.result_type), cursor.spelling, args)

def _assert(line):
    return "r = %-128ls assert(r >= asSUCCESS);" % line

typedef = {}

def get_real_type(name):
    while name in typedef:
        name = typedef[name]
    return name

def walk(cursor):
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.MACRO_DEFINITION:
            tokens = cindex.tokenize(tu, child.extent)
            if tokens[0].kind == cindex.TokenKind.IDENTIFIER and tokens[1].kind == cindex.TokenKind.LITERAL and is_int(tokens[1].spelling):
                print _assert("engine->RegisterEnumValue(\"HASH_DEFINES\", \"%s\", %s);" % (tokens[0].spelling, tokens[1].spelling))
        elif child.kind == cindex.CursorKind.FUNCTION_DECL:
           decl = get_function_def(child)
           print _assert("engine->RegisterGlobalFunction(\"%s %s(%s)\", asFUNCTIONPR(%s, (%s), %s), asCALL_CDECL);" % (decl[0], decl[1], decl[2], decl[1], decl[2], decl[0]))
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
                print _assert("engine->RegisterTypedef(\"%s\", \"%s\");" % (name, get_real_type(kind)))
            else:
                data = ""
                for token in tokens:
                    data += token.spelling + " "
                sys.stderr.write("Warning, typedef too complex, ignoring: %s\n" % data)

        else:
            sys.stderr.write("Warning, unhandled cursor: %s, %s\n" % (child.displayname, child.kind))

walk(tu.cursor)

for diag in tu.diagnostics:
    sys.stderr.write("Warning, clang had the following to say: %s\n" % (diag.spelling))
