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


def get_function_def(cursor):
    args = ""
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.PARM_DECL:
            if len(args):
                args += ", "
            args += get_type(child.type)

    return "%s %s(%s)" % (get_type(cursor.result_type), cursor.spelling, args)

def walk(cursor):
    for child in cursor.get_children():
        if child.kind == cindex.CursorKind.MACRO_DEFINITION:
            tokens = cindex.tokenize(tu, child.extent)
            if tokens[0].kind == cindex.TokenKind.IDENTIFIER and tokens[1].kind == cindex.TokenKind.LITERAL:
                print tokens[0].spelling, tokens[1].spelling
        elif child.kind == cindex.CursorKind.FUNCTION_DECL:
            print get_function_def(child)
        else:
            print child.displayname, child.kind

walk(tu.cursor)

for diag in tu.diagnostics:
    print diag.spelling
