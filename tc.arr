#lang pyret

import pyret-eval as E
import ast as A
import directory as D
import file as F
import Racket as Racket

data Pair:
  | pair(a,b)
end
# This isn't actually sufficient; should be a list of K,V pairs
fun <K,V> Map(o): List(o) end
fun <K,V> map-get(m :: Map<K,V>, k :: K) -> option.Option<V>:
  cases(List) m:
    | empty => option.none
    | link(f,r) => if k == f.a: option.some(f.b) else: map-get(r,k) end
  end
where:
  map-get([pair(1,3),pair('f',7)], 'f') is option.some(7)
  map-get([pair(1,3),pair('f',7)], 'fo') is option.none
end
fun concat(l :: List<List>) -> List:
  l.foldr(fun(f,r): f.append(r) end, [])
where:
  concat([[1],[2,3,4],[]]) is [1,2,3,4]
  concat([]) is []
  concat([[],[],[1]]) is [1]
end

data Type:
  | baseType(tags :: TagType, record :: RecordType)
  | arrowType(args :: List<Type>, ret :: Type, record :: RecordType)
end

data TagType:
  | topTag
  | botTag
  | baseTag(name :: String)
  | unionTag(ts :: List<Tag>)
end

data RecordType:
  | normalRecord(fields :: Map<String,Type>)
    # NOTE(dbp 2013-10-16): For when we know there are more fields, but aren't sure what they are.
    # this happens because of computed field names.
  | moreRecord(fields :: Map<String,Type>)
end

# Template for structural recursion
# cases(A.Expr) get-expr(ast):
#   | s_block(l, stmts) =>
#   | s_user_block(l, block) =>
#   | s_var(l, name, val) =>
#   | s_let(l, name, val) =>
#   | s_assign(l, id, val) =>
#   | s_if(l, branches) =>
#   | s_lam(l, ps, args, ann, doc, body, ck) =>
#   | s_method(l, args, ann, doc, body, ck) =>
#   | s_extend(l, super, fields) =>
#   | s_update(l, super, fields) =>
#   | s_obj(l, fields) =>
#   | s_app(r, fn, args) =>
#   | s_id(l, id) =>
#   | s_num(l, num) =>
#   | s_bool(l, bool) =>
#   | s_str(l, str) =>
#   | s_get_bang(l, obj, str) =>
#   | s_bracket(l, obj, field) =>
#   | s_colon_bracket(l, obj, field) =>
# end

fun augment(ast-expr :: A.Expr) -> A.Expr:
  var node-id = 0
  fun augment-local(ast :: A.Expr) -> A.Expr:
    node-id := node-id + 1
    cases(A.Expr) ast:
      | s_block(l, stmts) =>
        A.s_block(l, stmts.map(augment-local)).{node-id: node-id}
      | s_user_block(l, block) =>
        A.s_user_block(l,augment-local(block)).{node-id: node-id}
      | s_var(l, name, val) =>
        A.s_var(l,name, augment-local(val)).{node-id: node-id}
      | s_let(l, name, val) =>
        A.s_let(l,name, augment-local(val)).{node-id: node-id}
      | s_assign(l, id, val) =>
        A.s_assign(l, id, augment-local(val)).{node-id: node-id}
      # | TODO(dbp 2013-10-02)
      # | s_if(l, branches) =>
      # | s_lam(l, ps, args, ann, doc, body, ck) =>
      # | s_method(l, args, ann, doc, body, ck) =>
      # | s_extend(l, super, fields) =>
      # | s_update(l, super, fields) =>
      # | s_obj(l, fields) =>
      # | s_app(r, fn, args) =>
      # | s_get_bang(l, obj, str) =>
      # | s_bracket(l, obj, field) =>
      # | s_colon_bracket(l, obj, field) =>
      | else => ast.{node-id: node-id}
    end
  end
  augment-local(ast-expr)
end

fun tc-prog(prog :: A.Program, env):
  tc(augment(prog.block), env)
  prog
end

fun get-type(ann :: A.Ann) -> Type:
  top-type = baseType(topTag, moreRecord([]))
  cases(A.Ann) ann:
    | a_blank => top-type
    | a_any => top-type
    | a_name(l, id) => baseType(baseTag(id), moreRecord([]))
    | a_arrow(l, args, ret) => arrowType(args.map(get-type), get-type(ret))
    | a_record(l, fields) => baseType(topTag, normalRecord(fields.map(fun(field): pair(field.name, get-type(field.ann)) end)))
  end
end

fun get-bindings(ast :: A.Expr, env) -> List<Pair<String, Type>>:
  doc: "This function implements let* like behavior"
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.foldl(fun(stmt, newenv): get-bindings(stmt, newenv) end, env)
    | s_user_block(l, block) => get-bindings(block, env)
      # NOTE(dbp 2013-10-16): I'm using the ann if it exists, otherwise the value.
    | s_var(l, name, val) =>
      if A.is-a_blank(name.ann):
        env + [pair(name.id, tc(val, env))]
      else:
        env + [pair(name.id, get-type(name.ann))]
      end
    | s_let(l, name, val) =>
      if A.is-a_blank(name.ann):
        env + [pair(name.id, tc(val, env))]
      else:
        env + [pair(name.id, get-type(name.ann))]
      end
    | s_if(l, branches) =>
      # NOTE(dbp 2013-10-16): Adds a bunch of copies of env... woops
      branches.map(get-bindings(_,env))^concat()
    | else => env
    # | s_assign(l, id, val) => []
    # | s_lam(l, ps, args, ann, doc, body, ck) => []
    # | s_method(l, args, ann, doc, body, ck) => []
    # | s_extend(l, super, fields) => []
    # | s_update(l, super, fields) => []
    # | s_obj(l, fields) => []
    # | s_app(r, fn, args) => []
    # | s_id(l, id) => []
    # | s_num(l, num) => []
    # | s_bool(l, bool) => []
    # | s_str(l, str) => []
    # | s_get_bang(l, obj, str) => []
    # | s_bracket(l, obj, field) => []
    # | s_colon_bracket(l, obj, field) => []
  end
end

fun subtype(child :: Type, parent :: Type) -> Bool:
  fun tag-subtype(childT :: TagType, parentT :: TagType) -> Bool:
    # not real yet
    (parentT == topTag) or (childT == parentT)
  end
  fun record-subtype(childR :: RecordType, parentR :: RecordType) -> Bool:
    fun match-child(parent-fields, child-fields):
      for fold(rv from true, fld from parent-fields):
      cases(option.Option) map-get(child-fields, fld.a):
        | none => false
        | some(cty) => rv and (subtype(cty, fld.b))
      end
    end
    end
    cases(RecordType) parentR:
      | normalRecord(p-fields) =>
        cases(RecordType) childR:
          | normalRecord(c-fields) =>
            match-child(p-fields, c-fields)
          | moreRecord(c-fields) =>
            # TODO(dbp 2013-10-16): figure out what to do about more
            match-child(p-fields, c-fields)
        end
      | moreRecord(p-fields) =>
        cases(RecordType) childR:
          | normalRecord(c-fields) =>
            match-child(p-fields, c-fields)
          | moreRecord(c-fields) =>
            # TODO(dbp 2013-10-16): figure out what to do about more
            match-child(p-fields, c-fields)
        end
    end
  end
  cases(Type) parent:
    | baseType(parenttags, parentrecord) =>
      cases(Type) child:
        | baseType(childtags, childrecord) =>
          tag-subtype(childtags, parenttags) and record-subtype(childrecord, parentrecord)
      end
  end
where:
  topType = baseType(topTag, moreRecord([]))
  subtype(topType, topType) is true
  numType = baseType(baseTag("Number"), moreRecord([]))
  subtype(numType, topType) is true
  subtype(topType, numType) is false

  fun recType(flds): baseType(topTag, normalRecord(flds)) end

  subtype(recType([pair("foo", topType)]), topType) is true
  subtype(recType([pair("foo", topType)]), recType([pair("foo", topType)])) is true
  subtype(recType([pair("foo", topType)]), recType([pair("foo", numType)])) is false
  subtype(recType([pair("foo", numType)]), recType([pair("foo", topType)])) is true
  subtype(recType([]), recType([pair("foo", numType)])) is false
  subtype(recType([pair("foo", numType), pair("bar", topType)]), recType([pair("foo", topType)])) is true
end

fun type-record-add(orig :: Type, field :: String, type :: Type) -> Type:
  cases(Type) orig:
    | baseType(tags, record) =>
      cases(RecordType) record:
        | normalRecord(fields) =>
          baseType(tags, normalRecord([pair(field, type)] + fields))
        | moreRecord(fields) =>
          baseType(tags, moreRecord([pair(field, type)] + fields))
      end
  end
where:
  my-type = baseType(topTag, normalRecord([]))
  type-record-add(my-type, "foo", my-type) is baseType(topTag, normalRecord([pair("foo", my-type)]))
  my-more-type = baseType(topTag, moreRecord([]))
  type-record-add(my-more-type, "foo", my-type) is baseType(topTag, moreRecord([pair("foo", my-type)]))
end

fun tc-member(ast :: A.Member, env) -> Option<Pair<String,Type>>:
  cases(A.Member) ast:
    | s_data_field(l, name, value) =>
      # NOTE(dbp 2013-10-14): This is a bummer, but if it isn't
      # immediately obviously a string, not sure what to do.
      cases(A.Expr) name:
        | s_str(l1, s) => some(pair(s, tc(value, env)))
        | else => none
      end
    | else => none
    # | s_mutable_field(l, name, ann, value)
    # | s_once_field(l, name, ann, value)
    # | s_method_field(
  end
end

fun tc(ast :: A.Expr, env) -> Type:
  top-type = baseType(topTag, moreRecord([]))
  newenv = get-bindings(ast,env)
  tc-curried = fun(expr): tc(expr, newenv) end
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.map(tc-curried).last()
    | s_user_block(l, block) => tc-curried(block)
    | s_var(l, name, val) => top-type
    | s_let(l, name, val) =>
      ty = tc-curried(val)
      bindty = get-type(name.ann)
      if not subtype(ty, bindty):
        raise("Type error: " + name.id + " (" + tostring(l) + ") has type " + torepr(bindty) + " and cannot be assigned a value of the wrong type: " + torepr(ty))
      else:
        ty
      end
    | s_assign(l, id, val) => top-type
    | s_if(l, branches) => top-type
    | s_lam(l, ps, args, ann, doc, body, ck) => top-type
    | s_method(l, args, ann, doc, body, ck) => top-type
    | s_extend(l, super, fields) =>
      base = tc-curried(super)
      for fold(ty from base, fld from fields):
        cases(option.Option) tc-member(fld, newenv):
            # NOTE(dbp 2013-10-14): this seems really bad... as we're
            # saying that if we can't figure it out, you can't use it...
          | none => ty
          | some(fldty) =>
            type-record-add(ty, fldty.a, fldty.b)
        end
      end
    | s_update(l, super, fields) => top-type
    | s_obj(l, fields) =>
      baseType(botTag, for fold(acc from normalRecord([]), f from fields):
          cases(option.Option) tc-member(f, newenv):
            | none => moreRecord(acc.fields)
              # NOTE(dbp 2013-10-16): This is a little bit of a hack -
              # to reuse the helper that wants to operate on types.
            | some(fty) => type-record-add(baseType(topTag,acc), fty.a, fty.b).record
          end
        end)
    | s_app(r, fn, args) => top-type
    | s_id(l, id) =>
      cases(option.Option) map-get(newenv, id):
        # we won't actually get here, because we do unboundness typechecking already
        | none => raise("Type error: " + id + " not bound (" + tostring(l) + ")")
        | some(ty) => ty
      end
    | s_num(l, num) => baseType(baseTag("Number"), moreRecord([]))
    | s_bool(l, bool) => baseType(baseTag("Bool"), moreRecord([]))
    | s_str(l, str) => baseType(baseTag("String"), moreRecord([]))
    | s_get_bang(l, obj, str) => top-type
    | s_bracket(l, obj, field) =>
      cases(A.Expr) field:
        | s_str(l1, s) =>
          cases(RecordType) tc-curried(obj).record:
            | normalRecord(fields) =>
              cases(option.Option) map-get(fields, s):
                | none => raise("Type error: field " + s + " not found on object at " + tostring(l))
                | some(ty) => ty
              end
            | moreRecord(fields) =>
              cases(option.Option) map-get(fields, s):
                | none => top-type # NOTE(dbp 2013-10-16): this should be a warning probably
                | some(ty) => ty
              end
          end
        # NOTE(dbp 2013-10-16): This is unfortunate, but...
        | else => top-type
      end
    | s_colon_bracket(l, obj, field) => top-type
  end
end



# basic testing harness
fun build-path(parts):
  parts.join-str("/")
end
fun str-ends-with(s1,s2):
  s1.substring(s1.length() - s2.length(), s1.length()) == s2
end
fun str-starts-with(s1,s2):
  s1.substring(0, s2.length()) == s2
end
fun strip-ext(s):
  s.substring(0, s.length() - 4)
end

fun is-code-file(path):
  path^str-ends-with(".arr") and (not path^str-starts-with("."))
end

fun eval-str(p, s):
  default-env = {list: list, error: error}
  top-type = baseType(topTag, moreRecord([]))
  type-env = [pair("Any", top-type), pair("list", baseType(botTag, moreRecord([pair("map", top-type)])))]
  prog = s^A.parse(p, { ["check"]: false}).post-desugar^tc-prog(type-env)
  E.eval(prog^A.to-native(), default-env, {})
end



# commandline invocation
var files = []
baseR = Racket("racket/base")
cmdlineargs = baseR("current-command-line-arguments")
fun usage():
  print("Usage:\n    raco pyret tc.arr tests (runs all tests)\n    raco pyret tc.arr file.arr (runs single file)\n\n(running basic unit tests)\n")
end
cmdlinelen = baseR("vector-length",cmdlineargs)
if cmdlinelen == 0:
  usage()
else:
  mode = baseR("vector-ref", cmdlineargs, cmdlinelen - 1)
  if mode == "tests":
    files := D.dir("tests").list().map(fun(path): build-path(["tests", path]) end)
  else if baseR("file-exists?", mode) and (not str-ends-with(mode, "tc.arr")):
    files := [mode]
  else:
    usage()
  end

  check:
  files.map(fun(path):
      when is-code-file(path):
        # NOTE(dbp 2013-09-29):
        # We run the .arr file. It expects to have a corresponding .out and .err files.
        # if .err is non-empty, we expect to see an error that matches the content of that
        # file. If it is empty, we expect the value that comes out of the .arr to match the
        # value that comes from the .out. Obviously, the .out files should be much simpler than
        # the .arr files.
        stripped = strip-ext(path)
        print("Running " + stripped)
        outpath = stripped + ".out"
        errpath = stripped + ".err"
        code = F.input-file(path).read-file()
        out = F.input-file(outpath).read-file()
        err = F.input-file(errpath).read-file()
        if err.length() <> 0:
          eval-str(path, code) raises err
        else:
          eval-str(path, code) is eval-str(outpath, out)
        end
      end
    end)
  end
end
