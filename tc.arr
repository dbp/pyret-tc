#lang pyret

import pyret-eval as E
import ast as A
import directory as D
import file as F
import Racket as Racket
Loc = error.Location
loc = error.location

data Result:
  | result(ast :: A.Program, query :: (NodeId -> Type),
           errors :: List<TypeError>, warnings :: List<TypeWarning>)
end

data TypeError:
  | typeError(location :: Loc, message :: String)
end

data TypeWarning:
  | typeWarning(location :: Loc, message :: String)
end

data Pair:
  | pair(a,b)
end
NodeId = is-number
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
  | dynType
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

# NOTE(dbp 2013-10-30): We include the env because we might want to inspect it. It is not
# there for dynamic scoping purposes.
data TCResult:
  | tcResult(type :: Type, errors :: List<TypeError>, warnings :: List<TypeWarning>, env) with:
    set-type(self, ty :: Type):
      tcResult(ty, self.errors, self.warnings, self.env)
    end,
    add-error(self, l :: Loc, er :: String):
      tcResult(self.type, self.errors + [typeError(l,er)], self.warnings, self.env)
    end,
    add-warning(self, l :: Loc, wn :: String):
      tcResult(self.type, self.errors, self.warnings + [typeWarning(l,wn)], self.env)
    end,
    merge-messages(self, other :: TCResult):
      tcResult(self.type, self.errors + other.errors, self.warnings + other.warnings, self.env)
    end
sharing:
  tostring(self):
    if (self.errors.length() == 0) and (self.warnings.length() == 0):
      "No type errors detected."
    else:
      "Errors:\n" + torepr(self.errors) + "\n\nWarnings:\n " + torepr(self.warnings)
    end
  end,
  format-errors(self):
    if (self.errors.length() == 0):
      "No type errors detected."
    else:
      "Errors:\n" + torepr(self.errors)
    end
  end
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

fun tc-prog(prog :: A.Program, iifs, env):
  tc(augment(prog.block), iifs, env)
end

fun get-type(ann :: A.Ann) -> Type:
  cases(A.Ann) ann:
    | a_blank => dynType
    | a_any => dynType
    | a_name(l, id) => baseType(baseTag(id), moreRecord([]))
    | a_arrow(l, args, ret) => arrowType(args.map(get-type), get-type(ret), moreRecord([]))
    | a_record(l, fields) => baseType(topTag, normalRecord(fields.map(fun(field): pair(field.name, get-type(field.ann)) end)))
    | else => dynType
  end
end

fun get-bindings(ast :: A.Expr, env) -> List<Pair<String, Type>>:
  doc: "This function implements letrec behavior"
  anyty = baseType(topTag, moreRecord([]))
  boolty = baseType(baseTag("Bool"), moreRecord([]))
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.foldl(fun(stmt, newenv): get-bindings(stmt, newenv) end, env)
    | s_user_block(l, block) => get-bindings(block, env)
      # NOTE(dbp 2013-10-16): I'm using the ann if it exists, otherwise the value.
    | s_var(l, name, val) =>
      if A.is-a_blank(name.ann):
        env + [pair(name.id, tc(val, [], env).type)]
      else:
        env + [pair(name.id, get-type(name.ann))]
      end
    | s_let(l, name, val) =>
      if A.is-a_blank(name.ann):
        env + [pair(name.id, tc(val, [], env).type)]
      else:
        env + [pair(name.id, get-type(name.ann))]
      end
    | s_if(l, branches) =>
      # NOTE(dbp 2013-10-16): Adds a bunch of copies of env... woops
      branches.map(get-bindings(_,env))^concat()
    | s_datatype(l, name, params, variants, _) =>
      variants.map(get-variant-bindings(name, _))^concat() +
      [pair(name, arrowType([anyty], boolty, moreRecord([])))] + env
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
where:
  fun gb-src(src):
    get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).post-desugar.block, [])
  end
  fun name-ty(name):
    baseType(baseTag("Number"), moreRecord([]))
  end
  gb-src("x = 2") is [pair("x", name-ty("Number"))]
  gb-src("x = 2 y = x") is [pair("x", name-ty("Number")),
                            pair("y", name-ty("Number"))]
end

fun get-variant-bindings(tname :: String, variant :: A.Variant(fun(v):
                                     A.is-s_datatype_variant(v) or
                                     A.is-s_datatype_singleton_variant(v) end)) ->
    List<Pair<String, Type>>:
  bigty = baseType(baseTag(tname), moreRecord([]))
  boolty = baseType(baseTag("Bool"), moreRecord([]))
  anyty = baseType(topTag, moreRecord([]))
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
    | s_datatype_variant(l, vname, members, constr) =>
      [pair(vname, arrowType(members.map(get-member-type), bigty, moreRecord([]))),
        pair("is-" + vname, arrowType([anyty], boolty, moreRecord([])))]
    | s_datatype_singleton_variant(l, vname, constr) =>
      [pair(vname, bigty),
        pair("is-" + vname, arrowType([anyty], boolty, moreRecord([])))]
  end
where:
  # NOTE(dbp 2013-10-30): I don't like writing tests with the ast written out
  # like this, as it seems fragile, but I don't think we have a way of parsing
  # fragments, and parsing larger programs and extracting the parts out doesn't
  # seem any less fragile
  dummy-loc = loc("dummy-file", -1, -1)
  footy = baseType(baseTag("Foo"), moreRecord([]))
  anyty = baseType(topTag, moreRecord([]))
  boolty = baseType(baseTag("Bool"), moreRecord([]))
  strty = baseType(baseTag("String"), moreRecord([]))
  get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self"))))
  is
  [pair("foo", arrowType([], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]

  get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self"))))
  is
  [pair("foo", arrowType([strty], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]


  get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self"))))
  is
  [pair("foo", arrowType([strty, boolty], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]

end

fun is-inferred-functions(ast :: A.Expr, env) -> List<Pair<String, Type>>:
  iif-curried = is-inferred-functions(_, env)
  fun find-is-pairs(name :: String, e :: A.Expr) -> List<Type>: # arrowType specifically
    cases(A.Expr) e:
      | s_block(l, stmts) => stmts.map(find-is-pairs(name, _))^concat()
      | s_check_test(l, op, left, right) =>
        if op == "opis":
          # NOTE(dbp 2013-10-21): Really simple for now - only if it is of form funname(args) is bar
          cases(A.Expr) left:
            | s_app(l1, fn, args) =>
              cases(A.Expr) fn:
                | s_id(l2, fname) =>
                  if fname == name:
                    # NOTE(dbp 2013-10-21): Not sending inferred fns in - is that okay?
                    [arrowType(args.map(fun(arg): tc(arg,[],env).type end),
                        tc(right, [], env).type, moreRecord([]))]
                  else:
                    []
                  end
                | else => []
              end
            | else => []
          end
        else:
          []
        end
      | else => []
    end
  end
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.map(iif-curried)^concat()
    | s_fun(l, name, params, args, ann, doc, body, ck) =>
      pairs = find-is-pairs(name, ck)
      # NOTE(dbp 2013-10-21): this should do an least upper bound, eventually.
      if pairs <> []:
        [pair(name, pairs.first)]
      else:
        []
      end
    | else => []
  end
where:
  fun iif-src(src):
    stx = A.parse(src,"anonymous-file", { ["check"]: false}).pre-desugar
    is-inferred-functions(stx.block, [])
  end
  baseRec = moreRecord([])
  numty = baseType(baseTag("Number"), baseRec)
  strty = baseType(baseTag("String"), baseRec)
  boolty = baseType(baseTag("Bool"), baseRec)
  iif-src("fun f(): 10 where: f() is 10 end") is [pair("f", arrowType([], numty, baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end") is
    [pair("f", arrowType([strty], boolty, baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: g() is 10 end") is
  [pair("f", arrowType([strty], boolty, baseRec)), pair("g", arrowType([], numty, baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: f() is 10 end") is
  [pair("f", arrowType([strty], boolty, baseRec))]
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
    | dynType => true
    | arrowType(parentargs, parentret, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | arrowType(childargs, childret, childrecord) =>
          for fold2(wt from subtype(childret, parentret), ct from childargs, pt from parentargs):
            wt and subtype(pt, ct)
          end
        | else => false
      end
    | baseType(parenttags, parentrecord) =>
      cases(Type) child:
        | dynType => true
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
      # NOTE(dbp 2013-10-16): Can we start treating this as something
      # better? moreRecord or something?
    | dynType => dynType
  end
where:
  my-type = baseType(topTag, normalRecord([]))
  type-record-add(my-type, "foo", my-type) is baseType(topTag, normalRecord([pair("foo", my-type)]))
  my-more-type = baseType(topTag, moreRecord([]))
  type-record-add(my-more-type, "foo", my-type) is baseType(topTag, moreRecord([pair("foo", my-type)]))
end

fun tc-member(ast :: A.Member, iifs, env) -> Option<Pair<String,Type>>:
  cases(A.Member) ast:
    | s_data_field(l, name, value) =>
      # NOTE(dbp 2013-10-14): This is a bummer, but if it isn't
      # immediately obviously a string, not sure what to do.
      cases(A.Expr) name:
        | s_str(l1, s) => some(pair(s, tc(value, iifs, env)))
        | else => none
      end
    | else => none
    # | s_mutable_field(l, name, ann, value)
    # | s_once_field(l, name, ann, value)
    # | s_method_field(
  end
end

fun tc(ast :: A.Expr, iifs, env) -> TCResult:
  newenv = get-bindings(ast,env)
  dynR = tcResult(dynType, [], [], newenv)
  nothingR = tcResult(baseType(baseTag("Nothing"), normalRecord([])), [], [], newenv)
  tc-curried = fun(expr): tc(expr, iifs, newenv) end
  cases(A.Expr) ast:
    | s_block(l, stmts) => stmts.foldr(fun(stmt, base):
        t = tc-curried(stmt)
        base.merge-messages(t).set-type(t.type)
        end, dynR)
    | s_user_block(l, block) => tc-curried(block)
    | s_var(l, name, val) => dynR
    | s_let(l, name, val) =>
      # NOTE(dbp 2013-10-21): Ugly hack. We want to find
      # desugared funs, so we look for let bindings. Our no-shadowing
      # rule actually makes this easier, because since the iifs are
      # all top level, if we find a binding anywhere that has that
      # name, it must be the function.
      bindty = get-type(name.ann)
      cases(option.Option) map-get(iifs, name.id):
        | none =>
          ty = tc-curried(val)
          if not subtype(ty.type, bindty):
            ty.set-type(dynType).add-error(l, name.id + " has type " + torepr(bindty) +
              " and cannot be assigned a value of the wrong type: " + torepr(ty))
          else:
            ty
          end
        | some(fty) =>
          # NOTE(dbp 2013-10-21): we want to type check the function
          # bound with our inferred type, unless they provided their
          # own type. In the case of a type error when inference was involved
          # we want to alter the error messages.
          cases(A.Expr) val:
            | s_lam(l1, ps, args, ann, doc, body, ck) =>
              # NOTE(dbp 2013-10-21): Gah, mutation. This code should be refactored.
              var inferred = false
              arg-tys = for map2(b from args, inf from fty.args):
                if A.is-a_blank(b.ann):
                  when inf <> dynType:
                    inferred := true
                  end
                  inf
                else:
                  get-type(b.ann)
                end
              end
              newenv1 = for map2(b from args, t from arg-tys):
                pair(b.id, t)
              end + newenv
              body-ty = tc(body, iifs, newenv1)
              ret-ty = if A.is-a_blank(ann): fty.ret else: get-type(ann) end
              if subtype(body-ty.type, ret-ty):
                body-ty.set-type(arrowType(arg-tys, ret-ty, moreRecord([])))
              else:
                body-ty.set-type(dynType).add-error(l, "the body of the function " + (if inferred: "was inferred based on tests with " else: "had " end) + "type " + tostring(body-ty) + ", which isn't a subtype of the functions return type, " + tostring(ann))
              end
            | else =>
              # NOTE(dbp 2013-10-21): This is a bizarre case. It means we no longer
              # understand the desugaring, so we really should abort and figure our stuff out.
              raise("Type Checker error: encountered a let binding that
                should have been a function, but wasn't (at loc " + torepr(l) + ")")
          end
      end
    | s_assign(l, id, val) => dynR
    | s_if(l, branches) => dynR
    | s_lam(l, ps, args, ann, doc, body, ck) =>
      newenv1 = args.map(fun(b): pair(b.id, get-type(b.ann)) end) + newenv
      body-ty = tc(body, iifs, newenv1)
      if subtype(body-ty.type, get-type(ann)):
        body-ty.set-type(arrowType(args.map(fun(b): get-type(b.ann) end), get-type(ann), moreRecord([])))
      else:
        body-ty.set-type(dynType).add-error(l, "the body of the function had type " + tostring(body-ty) + ", which isn't a subtype of the functions return type, " + tostring(ann))
      end
    | s_method(l, args, ann, doc, body, ck) => dynR
    | s_extend(l, super, fields) =>
      base = tc-curried(super)
      for fold(ty from base, fld from fields):
        cases(option.Option) tc-member(fld, iifs, newenv):
            # NOTE(dbp 2013-10-14): this seems really bad... as we're
            # saying that if we can't figure it out, you can't use it...
          | none => ty
          | some(fldty) =>
            ty.merge-messages(fldty.b).set-type(type-record-add(ty.type, fldty.a, fldty.b.type))
        end
      end
    | s_update(l, super, fields) => dynR
    | s_obj(l, fields) =>
      res = for fold(acc from pair(dynR, normalRecord([])), f from fields):
        cases(option.Option) tc-member(f, iifs, newenv):
          | none => pair(acc.a, moreRecord(acc.b.fields))
            # NOTE(dbp 2013-10-16): This is a little bit of a hack -
            # to reuse the helper that wants to operate on types.
          | some(fty) =>
            pair(acc.a.merge-messages(fty.b),
              type-record-add(baseType(topTag,acc.b), fty.a, fty.b.type).record)
        end
      end
      res.a.set-type(baseType(botTag, res.b))
    | s_app(l, fn, args) =>
      fn-ty = tc-curried(fn)
      cases(Type) fn-ty.type:
        | arrowType(arg-types, ret-type, rec-type) =>
          if args.length() <> arg-types.length():
            fn-ty.set-type(dynType).add-error(l, "arity mismatch: function expected " +
              tostring(arg-types.length()) + " arguments and was passed " + tostring(args.length()))
          else:
            arg-vals = args.map(tc-curried)
            # NOTE(dbp 2013-10-21): collect messages from type checking
            base-type = arg-vals.foldr(fun(arg, base): base.merge-messages(arg) end,
              fn-ty.set-type(ret-type))
            var counter = 1
            for fold2(ty from base-type, at from arg-types, av from arg-vals):
              if not subtype(av.type, at):
                ty.add-error(l, "argument number " + tostring(counter) +
                  " passed to the function is of the wrong type. Expected " +
                  torepr(at) + ", but got " + torepr(av.type))
              else:
                ty
              end
            end
          end
          # NOTE(dbp 2013-10-16): Not really anything we can do. Odd, but...
        | dynType => dynR
        | else =>
          fn-ty.add-error(l, "applying a non-function with type " + torepr(fn-ty)).set-type(dynType)
      end
    | s_id(l, id) =>
      cases(option.Option) map-get(newenv, id):
        # we won't actually get here, because we do unboundness typechecking already
        | none => dynR.add-error(l, id + " not bound")
        | some(ty) => tcResult(ty,[],[],newenv)
      end
    | s_num(l, num) => tcResult(baseType(baseTag("Number"), moreRecord([])),[],[],newenv)
    | s_bool(l, bool) => tcResult(baseType(baseTag("Bool"), moreRecord([])),[],[],newenv)
    | s_str(l, str) => tcResult(baseType(baseTag("String"), moreRecord([])),[],[],newenv)
    | s_get_bang(l, obj, str) => dynR
    | s_bracket(l, obj, field) =>
      cases(A.Expr) field:
        | s_str(l1, s) =>
          obj-ty = tc-curried(obj)
          cases(Type) obj-ty.type:
            | dynType => obj-ty
            | else =>
              cases(RecordType) obj-ty.type.record:
                | normalRecord(fields) =>
                  cases(option.Option) map-get(fields, s):
                    | none => obj-ty.add-error(l, "field " + s + " not found on object")
                    | some(ty) => obj-ty.set-type(ty)
                  end
                | moreRecord(fields) =>
                  cases(option.Option) map-get(fields, s):
                    | none => obj-ty.add-warning(l, "field " + s +
                        " may not exist on object.").set-type(dynType)
                    | some(ty) => obj-ty.set-type(ty)
                  end
              end
          end
        | else =>
          # NOTE(dbp 2013-10-21): Actually type check field to see if it is a String or Dyn
          dynR.add-warning(l, "computed field access can cause runtime errors.")
      end
    | s_colon_bracket(l, obj, field) => dynR
    | s_datatype(l, name, params, variants, check) =>
      # NOTE(dbp 2013-10-30): Should statements have type nothing?
      nothingR
    | s_cases(l, type, val, branches) => dynR #TODOTODOTODO
    | else => raise("tc: no case matched for: " + torepr(ast))
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

fun tc-file(p, s):
  top-type = baseType(topTag, moreRecord([]))
  type-env = [
    pair("Any", top-type),
    pair("list", baseType(botTag,
        moreRecord([pair("map", top-type)]))),
     pair("builtins", baseType(botTag,
        moreRecord([])))
  ]
  stx = s^A.parse(p, { ["check"]: false})
  iifs = is-inferred-functions(stx.pre-desugar.block, type-env)
  resultty = tc-prog(stx.with-types, iifs, type-env)
  # print(resultty.env.map(torepr).join-str("\n"))
  resultty
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
        # We run the .arr file. It expects to have a corresponding .err file.
        # if .err is non-empty, we expect to see an error that matches the content of that
        # file. If it is empty, we expect it to produce nothing as the output of type checking.
        stripped = strip-ext(path)
        print("Running " + stripped)
        errpath = stripped + ".err"
        code = F.input-file(path).read-file()
        err = F.input-file(errpath).read-file()
        if err.length() <> 0:
          msg = tc-file(path, code).format-errors()
          pair(path,pair(msg, msg.contains(err))) is pair(path, pair(msg, true))
        else:
          msg = tc-file(path, code).format-errors()
          pair(path, pair(msg, msg.contains("No type errors detected."))) is pair(path,pair(msg, true))
        end
      end
    end)
  end
end
