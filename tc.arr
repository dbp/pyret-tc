#lang pyret

import pyret-eval as E
import ast as A
import directory as D
import file as F

# This isn't actually sufficient; should be a list of K,V pairs
data Pair:
  | pair(a,b)
end
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
  | arrowType(args :: List<Type>, ret :: Type)
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

fun get-bindings(ast :: A.Expr) -> List<Pair<String, Ty>>:
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.map(get-bindings)^concat()
    | s_user_block(l, block) => get-bindings(block)
    | s_var(l, name, val) => [pair(name.id, get-type(name.ann))]
    | s_let(l, name, val) => [pair(name.id, get-type(name.ann))]
    | s_assign(l, id, val) => []
    | s_if(l, branches) => branches.map(get-bindings)^concat()
    | s_lam(l, ps, args, ann, doc, body, ck) => []
    | s_method(l, args, ann, doc, body, ck) => []
    | s_extend(l, super, fields) => []
    | s_update(l, super, fields) => []
    | s_obj(l, fields) => []
    | s_app(r, fn, args) => []
    | s_id(l, id) => []
    | s_num(l, num) => []
    | s_bool(l, bool) => []
    | s_str(l, str) => []
    | s_get_bang(l, obj, str) => []
    | s_bracket(l, obj, field) => []
    | s_colon_bracket(l, obj, field) => []
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
  newenv = env.append(get-bindings(ast))
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
        cases(option.Option) tc-member(fld, env):
            # NOTE(dbp 2013-10-14): this seems really bad... as we're
            # saying that if we can't figure it out, you can't use it...
          | none => ty
          | some(fldty) =>
            type-record-add(ty, fldty.a, fldty.b)
        end
      end
    | s_update(l, super, fields) => top-type
    | s_obj(l, fields) => top-type # FIXME(dbp 2013-10-16): top-type is WRONG
    | s_app(r, fn, args) => top-type
    | s_id(l, id) =>
          # we won't actually get here, because we do unboundness typechecking already
      cases(option.Option) map-get(newenv, id):
        | none => raise("Type error: " + id + " not bound (" + tostring(l) + ")")
        | some(ty) => ty
      end
    | s_num(l, num) => baseType(baseTag("Number"), moreRecord([]))
    | s_bool(l, bool) => baseType(baseTag("Bool"), moreRecord([]))
    | s_str(l, str) => baseType(baseTag("String"), moreRecord([]))
    | s_get_bang(l, obj, str) => top-type
    | s_bracket(l, obj, field) => top-type
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
  type-env = [pair("Any", top-type)]
  prog = s^A.parse(p, { ["check"]: false}).post-desugar^tc-prog(type-env)
  E.eval(prog^A.to-native(), default-env, {})
end

D.dir("tests").list().map(fun(path):
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
      code = F.input-file(build-path(["tests", path])).read-file()
      out = F.input-file(build-path(["tests", outpath])).read-file()
      err = F.input-file(build-path(["tests", errpath])).read-file()
      check:
      if err.length() <> 0:
        eval-str(path, code) raises err
      else:
        eval-str(path, code) is eval-str(outpath, out)
      end
    end
  end
end)