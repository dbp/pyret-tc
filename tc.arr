#lang pyret

################################################################################
#                                                                              #
# This file contains a type checker for the Pyret language.                    #
# All work (c) 2013 Daniel Patterson <dbp@dbpmail.net>.                        #
#                                                                              #
# Permission to use, copy, modify, and/or distribute this software for         #
# any purpose with or without fee is hereby granted, provided that the         #
# above copyright notice and this permission notice appear in all              #
# copies.                                                                      #
#                                                                              #
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL                #
# WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED                #
# WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE             #
# AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL         #
# DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA           #
# OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER            #
# TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR             #
# PERFORMANCE OF THIS SOFTWARE.                                                #
#                                                                              #
################################################################################

import pyret-eval as E
import ast as A
import directory as D
import file as F
import Racket as Racket
Loc = error.Location
loc = error.location


################################################################################
# Datatype definitions.                                                        #
################################################################################

data Pair:
  | pair(a,b)
sharing:
  _equals(self, other):
    (self.a == other.a) and (self.b == other.b)
  end,
  chain(self, op, other):
    pair(op(self.a, other.a), op(self.b, other.b))
  end,
  chainl(self, op, arg):
    pair(op(self.a, arg), self.b)
  end,
  chainr(self, op, arg):
    pair(self.a, op(self.b, arg))
  end
end

data TypeError:
  | typeError(location :: Loc, message :: String)
end

data Type:
  | dynType
  | baseType(tag :: TagType, record :: RecordType)
  | arrowType(args :: List<Type>, ret :: Type, record :: RecordType)
sharing:
  _equals(self, other):
    cases(Type) self:
      | dynType => is-dynType(other)
      | baseType(tag, record) =>
        is-baseType(other) and (tag == other.tag) and (record == other.record)
      | arrowType(args, ret, record) =>
        is-arrowType(other) and (args == other.args)
        and (ret == other.ret) and (record == other.record)
    end
  end
end

data TagType:
  | topTag
  | botTag
  | baseTag(name :: String)
sharing:
  _equals(self, other):
    cases(TagType) self:
      | topTag => is-topTag(other)
      | botTag => is-botTag(other)
      | baseTag(name) => is-baseTag(other) and (name == other.name)
    end
  end
end

fun <K,V> Map(o): List(o) end

data RecordType:
  | normalRecord(fields :: Map<String,Type>)
    # NOTE(dbp 2013-10-16): For when we know there are more fields,
    # but aren't sure what they are.
  | moreRecord(fields :: Map<String,Type>)
sharing:
  _equals(self, other):
    cases(RecordType) self:
      | normalRecord(fields) => is-normalRecord(other) and (fields == other.fields)
      | moreRecord(fields) => is-moreRecord(other) and (fields == other.fields)
    end
  end
end


# NOTE(dbp 2013-10-30): env included for debugging / tooling. It
# should never be used for typechecking.
data TCResult:
  | tcResult(type :: Type, errors :: List<TypeError>, env, type-env) with:
    set-type(self, ty :: Type):
      tcResult(ty, self.errors, self.env, self.type-env)
    end,
    add-error(self, l :: Loc, er :: String):
      tcResult(self.type, self.errors + [typeError(l,er)], self.env, self.type-env)
    end,
    merge-messages(self, other :: TCResult):
      tcResult(self.type, self.errors + other.errors, self.env, self.type-env)
    end
sharing:
  format-errors(self):
    if (self.errors.length() == 0):
      "No type errors detected."
    else:
      "Errors:\n" + torepr(self.errors)
    end
  end
end


################################################################################
# Error message definitions.                                                   #
################################################################################

data TCError:
  | errAssignWrongType with: tostring(self):
      "A name was defined to have a certain type,
      but assigned a value of an incompatible type."
    end
  | errFunctionInferredIncompatibleReturn with: tostring(self):
      "The body of the function is incompatible with the return
      type inferred based on tests."
    end
  | errFunctionAnnIncompatibleReturn with: tostring(self):
      "The body of the function is incompatible with the return
      type specified in annotations"
    end
  | errArityMismatch with: tostring(self):
      "Arity mismatch: function expected a different number of arguments
      than it was given."
    end
  | errArgumentBadType with: tostring(self):
      "An argument passed to the function is of the wrong type."
    end
  | errApplyNonFunction with: tostring(self):
      "Applying a non-function."
    end
  | errUnboundIdentifier with: tostring(self):
      "Identifier is unbound."
    end
  | errFieldNotFound with: tostring(self):
      "Field not found on object."
    end
  | errCasesValueBadType with: tostring(self):
      "Value in cases expression is not of the right type."
    end
  | errCasesBranchInvalidVariant with: tostring(self):
      "A branch in the cases expression is
      not a valid variant of the data type."
    end
  | errCasesPatternNumberFields with: tostring(self):
      "A variant pattern for a cases branch does not
      have the right number of fields."
    end
  | errCasesBranchType with: tostring(self):
      "All branches of a cases expression must evaluate
      to the same type."
    end
  | errTypeNotDefined with: tostring(self):
      "A type was used that is not defined. Did you forget to
      import, or forget to add the type parameter?"
    end
end

fun msg(err :: TCError, values :: List<Any>) -> String:
  "An error occurred during type-checking:\n\n" + tostring(err) +
  "\n\nRelated values:\n\n" + values.map(torepr).join-str(", ")
end

fun fmty(type :: Type) -> String:
  torepr(type)
end

################################################################################
# Non-typechecking related helper functions.                                   #
################################################################################

fun <K,V> map-get(m :: Map<K,V>, k :: K) -> Option<V>:
  cases(List) m:
    | empty => none
    | link(f,r) => if k == f.a: some(f.b) else: map-get(r,k) end
  end
where:
  map-get([pair(1,3),pair('f',7)], 'f') is some(7)
  map-get([pair(1,3),pair('f',7)], 'fo') is none
end

fun concat(l :: List<List>) -> List:
  l.foldr(fun(f,r): f.append(r) end, [])
where:
  concat([[1],[2,3,4],[]]) is [1,2,3,4]
  concat([]) is []
  concat([[],[],[1]]) is [1]
end


################################################################################
# Basic helper functions.                                                      #
################################################################################

fun nmty(name :: String) -> Type:
  baseType(baseTag(name), moreRecord([]))
end

fun get-type(ann :: A.Ann) -> Type:
  cases(A.Ann) ann:
    | a_blank => dynType
    | a_any => dynType
    | a_name(l, id) => nmty(id)
    | a_arrow(l, args, ret) => arrowType(args.map(get-type), get-type(ret), moreRecord([]))
    | a_record(l, fields) =>
      baseType(
        topTag,
        normalRecord(fields.map(fun(field): pair(field.name, get-type(field.ann)) end))
        )
    | else => dynType
  end
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
  type-record-add(my-type, "foo", my-type)
    is baseType(topTag, normalRecord([pair("foo", my-type)]))
  my-more-type = baseType(topTag, moreRecord([]))
  type-record-add(my-more-type, "foo", my-type)
    is baseType(topTag, moreRecord([pair("foo", my-type)]))
end


################################################################################
# Binding extraction, letrec behavior, datatype bindings.                      #
################################################################################

fun get-bindings(ast :: A.Expr, envs) -> Pair<List<Pair<String, Type>>,List<String>>:
  doc: "This function implements letrec behavior."
  anyty = baseType(topTag, moreRecord([]))
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      stmts.foldl(fun(stmt, newenvs):
          get-bindings(stmt, newenvs)
        end, envs)
    | s_user_block(l, block) => get-bindings(block, envs)
      # NOTE(dbp 2013-10-16): Use the ann if it exists, otherwise the type of value.
    | s_var(l, name, val) =>
      if A.is-a_blank(name.ann):
        envs.chainl((_+_), [pair(name.id, tc(val, [], envs.a, envs.b).type)])
      else:
        envs.chainl((_+_), [pair(name.id, get-type(name.ann))])
      end
    | s_let(l, name, val) =>
      if A.is-a_blank(name.ann):
        envs.chainl((_+_), [pair(name.id, tc(val, [], envs.a, envs.b).type)])
      else:
        envs.chainl((_+_), [pair(name.id, get-type(name.ann))])
      end
      # NOTE(dbp 2013-11-01): Not including, as bindings inside ifs shouldn't escape
    # | s_if(l, branches) =>
    #   # NOTE(dbp 2013-10-16): Adds a bunch of copies of env... woops
    #   branches.map(get-bindings(_,envs)).foldl(
    #     fun(binds, base): base.chain((_+_), binds) end, envs
    #     )
    | s_datatype(l, name, params, variants, _) =>
      variants.map(get-variant-bindings(name, _)).foldl(
        fun(binds, base): base.chainl((_+_), binds) end,
        envs.chainl((_+_), [pair(name, arrowType([anyty], nmty("Bool"), moreRecord([])))])
        )
    | else => envs
  end
where:
  fun gb-src(src):
    get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).post-desugar.block,
      pair([], default-type-env))
  end
  fun name-ty(name):
    baseType(baseTag("Number"), moreRecord([]))
  end
  gb-src("x = 2") is pair([pair("x", name-ty("Number"))], default-type-env)
  gb-src("x = 2 y = x") is pair([pair("x", name-ty("Number")),
                            pair("y", name-ty("Number"))], default-type-env)
end

fun get-variant-bindings(tname :: String, variant :: A.Variant(fun(v):
                                     A.is-s_datatype_variant(v) or
                                     A.is-s_datatype_singleton_variant(v) end)) ->
    List<Pair<String, Type>>:
  bigty = baseType(baseTag(tname), moreRecord([]))
  anyty = baseType(topTag, moreRecord([]))
  boolty = baseType(baseTag("Bool"), moreRecord([]))
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


################################################################################
# is-inference: inferring types from the way they are used in check-blocks.    #
################################################################################

fun is-inferred-functions(ast :: A.Expr, env, type-env) -> List<Pair<String, Type>>:
  iif-curried = is-inferred-functions(_, env, type-env)
  fun find-is-pairs(name :: String, e :: A.Expr) -> List<Type>:
    cases(A.Expr) e:
      | s_block(l, stmts) => stmts.map(find-is-pairs(name, _))^concat()
      | s_check_test(l, op, left, right) =>
        if op == "opis":
          # NOTE(dbp 2013-10-21): Really simple for now - only if it
          # is of form funname(args) is bar.
          cases(A.Expr) left:
            | s_app(l1, fn, args) =>
              cases(A.Expr) fn:
                | s_id(l2, fname) =>
                  if fname == name:
                    # QUESTION(dbp 2013-10-21): Not sending inferred fns in - is that okay?
                    [arrowType(args.map(fun(arg): tc(arg,[],env,type-env).type end),
                        tc(right, [], env, type-env).type, moreRecord([]))]
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
      # NOTE(dbp 2013-10-21): this should do an least upper bound.
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
    is-inferred-functions(stx.block, [], default-type-env)
  end
  baseRec = moreRecord([])
  iif-src("fun f(): 10 where: f() is 10 end") is
    [pair("f", arrowType([], nmty("Number"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end") is
    [pair("f", arrowType([nmty("String")], nmty("Bool"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: g() is 10 end") is
    [pair("f", arrowType([nmty("String")], nmty("Bool"), baseRec)),
    pair("g", arrowType([], nmty("Number"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: f() is 10 end") is
  [pair("f", arrowType([nmty("String")], nmty("Bool"), baseRec))]
end


################################################################################
# Subtyping (mostly record-based.)                                             #
################################################################################

fun subtype(child :: Type, parent :: Type) -> Bool:
  fun tag-subtype(childT :: TagType, parentT :: TagType) -> Bool:
    # not real yet
    (parentT == topTag) or (childT == parentT)
  end
  fun record-subtype(childR :: RecordType, parentR :: RecordType) -> Bool:
    fun match-child(parent-fields, child-fields):
      for fold(rv from true, fld from parent-fields):
      cases(Option) map-get(child-fields, fld.a):
        | none => false
        | some(cty) => rv and (subtype(cty, fld.b))
      end
    end
    end
    fun fields-child(fields):
      cases(RecordType) childR:
          | normalRecord(c-fields) =>
            match-child(fields, c-fields)
          | moreRecord(c-fields) =>
            # TODO(dbp 2013-10-16): figure out what to do about more
            match-child(fields, c-fields)
        end
    end
    cases(RecordType) parentR:
      | normalRecord(p-fields) => fields-child(p-fields)
      | moreRecord(p-fields) => fields-child(p-fields)
    end
  end

  cases(Type) parent:
    | dynType => true
    | arrowType(parentargs, parentret, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | arrowType(childargs, childret, childrecord) =>
          for fold2(wt from subtype(childret, parentret),
                    ct from childargs,
                    pt from parentargs):
            wt and subtype(pt, ct)
          end
        | else => false
      end
    | baseType(parenttags, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | baseType(childtags, childrecord) =>
          tag-subtype(childtags, parenttags) and
          record-subtype(childrecord, parentrecord)
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
  subtype(recType([pair("foo", numType), pair("bar", topType)]),
    recType([pair("foo", topType)])) is true
end


################################################################################
# tc Helper functions.                                                         #
################################################################################

default-type-env = [
  "Bool",
  "Number",
  "String",
  "Any",
  "List",
  "Nothing"
]

fun tc-file(p, s):
  top-type = baseType(topTag, moreRecord([]))
  env = [
    pair("Any", top-type),
    pair("list", baseType(botTag,
        moreRecord([pair("map", top-type)]))),
    pair("builtins", baseType(botTag,
        moreRecord([]))),
    pair("link", arrowType([dynType, dynType], nmty("List"), moreRecord([]))),
    pair("empty", nmty("List"))
  ]
  stx = s^A.parse(p, { ["check"]: false})
  iifs = is-inferred-functions(stx.pre-desugar.block, env, default-type-env)
  resultty = tc-prog(stx.with-types, iifs, env, default-type-env)
  # print(resultty.env.map(torepr).join-str("\n"))
  resultty
end

fun tc-prog(prog :: A.Program, iifs, env, type-env):
  tc(prog.block, iifs, env, type-env)
end

fun tc-member(ast :: A.Member, iifs, env, type-env) -> Option<Pair<String,Type>>:
  cases(A.Member) ast:
    | s_data_field(l, name, value) =>
      # NOTE(dbp 2013-10-14): This is a bummer, but if it isn't
      # immediately obviously a string, not sure what to do.
      cases(A.Expr) name:
        | s_str(l1, s) => some(pair(s, tc(value, iifs, env, type-env)))
        | else => none
      end
    | else => none
    # | s_mutable_field(l, name, ann, value)
    # | s_once_field(l, name, ann, value)
    # | s_method_field(
  end
end


################################################################################
# Main typechecking function.                                                  #
################################################################################

fun tc(ast :: A.Expr, iifs, _env, _type-env) -> TCResult:
  newenvs = get-bindings(ast,pair(_env,_type-env))
  env = newenvs.a
  type-env = newenvs.b
  dynR = tcResult(dynType, [], env, type-env)
  nothingR = tcResult(nmty("Nothing"), [], env, type-env)
  tc-curried = fun(expr): tc(expr, iifs, env, type-env) end
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
            ty.set-type(dynType).add-error(l,
              msg(errAssignWrongType,
                [name.id, fmty(bindty), fmty(ty.type)])
              )
          else:
            ty
          end
        | some(fty) =>
          # NOTE(dbp 2013-10-21): we want to type check the function
          # bound with our inferred type, unless they provided their
          # own type. In the case of a type error when inference was
          # involved we want to alter the error messages.
          cases(A.Expr) val:
            | s_lam(l1, ps, args, ann, doc, body, ck) =>
              # NOTE(dbp 2013-10-21): Gah, mutation. This code should
              # be refactored.
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
              env1 = for map2(b from args, t from arg-tys):
                pair(b.id, t)
              end + env
              body-ty = tc(body, iifs, env1, type-env)
              ret-ty = if A.is-a_blank(ann): fty.ret else: get-type(ann) end
              if subtype(body-ty.type, ret-ty):
                body-ty.set-type(arrowType(arg-tys, ret-ty, moreRecord([])))
              else:
                body-ty.set-type(dynType).add-error(l,
                  if inferred:
                    msg(errFunctionInferredIncompatibleReturn,
                      [fmty(body-ty), fmty(ret-ty)])
                  else:
                    msg(errFunctionAnnIncompatibleReturn,
                      [fmty(body-ty), fmty(ret-ty)])
                  end)
              end
            | else =>
              # NOTE(dbp 2013-10-21): This is a bizarre case. It means
              # we no longer understand the desugaring, so we really
              # should abort and figure our stuff out.
              raise("Type Checker error: encountered a let binding that
                should have been a function, but wasn't (at loc " +
                torepr(l) + ")")
          end
      end
    | s_assign(l, id, val) => dynR
    | s_if(l, branches) => dynR
    | s_lam(l, ps, args, ann, doc, body, ck) =>
      env1 = args.map(fun(b): pair(b.id, get-type(b.ann)) end) + env
      body-ty = tc(body, iifs, env1, type-env)
      if subtype(body-ty.type, get-type(ann)):
        body-ty.set-type(
          arrowType(args.map(fun(b): get-type(b.ann) end),
            get-type(ann), moreRecord([]))
          )
      else:
        body-ty.set-type(dynType).add-error(l,
          msg(errFunctionAnnIncompatibleReturn,
            [fmty(body-ty), fmty(get-type(ann))]))
      end
    | s_method(l, args, ann, doc, body, ck) => dynR
    | s_extend(l, super, fields) =>
      base = tc-curried(super)
      for fold(ty from base, fld from fields):
        cases(Option) tc-member(fld, iifs, env, type-env):
            # NOTE(dbp 2013-10-14): this seems really bad... as we're
            # saying that if we can't figure it out, you can't use it...
          | none => ty
          | some(fldty) =>
            ty.merge-messages(fldty.b).set-type(
              type-record-add(ty.type, fldty.a, fldty.b.type)
              )
        end
      end
    | s_update(l, super, fields) => dynR
    | s_obj(l, fields) =>
      res = for fold(acc from pair(dynR, normalRecord([])), f from fields):
        cases(option.Option) tc-member(f, iifs, env, type-env):
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
            fn-ty.set-type(dynType).add-error(l,
              msg(errArityMismatch, [arg-types.length(), args.length()]))
          else:
            arg-vals = args.map(tc-curried)
            # NOTE(dbp 2013-10-21): collect messages from type checking
            base-type = arg-vals.foldr(fun(arg, base): base.merge-messages(arg) end,
              fn-ty.set-type(ret-type))
            var counter = 1
            for fold2(ty from base-type, at from arg-types, av from arg-vals):
              if not subtype(av.type, at):
                ty.add-error(l,
                  msg(errArgumentBadType, [counter, fmty(at), fmty(av.type)]))
              else:
                ty
              end
            end
          end
          # NOTE(dbp 2013-10-16): Not really anything we can do. Odd, but...
        | dynType => dynR
        | else =>
          fn-ty.add-error(l, msg(errApplyNonFunction, [fmty(fn-ty)])).set-type(dynType)
      end
    | s_id(l, id) =>
      cases(option.Option) map-get(env, id):
        # we won't actually get here, because we do unboundness typechecking already
        | none => dynR.add-error(l, msg(errUnboundIdentifier, [id]))
        | some(ty) => tcResult(ty,[],env,type-env)
      end
    | s_num(l, num) => tcResult(baseType(baseTag("Number"), moreRecord([])),[],env,type-env)
    | s_bool(l, bool) => tcResult(baseType(baseTag("Bool"), moreRecord([])),[],env,type-env)
    | s_str(l, str) => tcResult(baseType(baseTag("String"), moreRecord([])),[],env,type-env)
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
                  cases(Option) map-get(fields, s):
                    | none => obj-ty.add-error(l, msg(errFieldNotFound, [s]))
                    | some(ty) => obj-ty.set-type(ty)
                  end
                | moreRecord(fields) =>
                  cases(Option) map-get(fields, s):
                    | none => obj-ty.set-type(dynType)
                    | some(ty) => obj-ty.set-type(ty)
                  end
              end
          end
        | else =>
          # NOTE(dbp 2013-10-21): Actually type check field to see if
          # it is a String or Dyn
          dynR
      end
    | s_colon_bracket(l, obj, field) => dynR
    | s_datatype(l, name, params, variants, check) =>
      # NOTE(dbp 2013-10-30): Should statements have type nothing?
      nothingR
    | s_cases(l, _type, val, branches) =>
      type = get-type(_type)
      val-ty = tc-curried(val)
      if not subtype(type, val-ty.type):
        dynR.add-error(l,
          msg(errCasesValueBadType, [fmty(type), fmty(val-ty.type)])
          )
      else:
        branches.foldr(fun(branch, ty-ers):
            # TODO(dbp 2013-10-30): Need to have a data-env, so we can
            # pick up non-bound constructors.
            cases(Option) map-get(env, branch.name):
              | none => ty-ers.add-error(branch.l,
                  msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                  )
              | some(ty) =>
                cases(Type) ty:
                  | arrowType(args, ret, rec) =>
                    # NOTE(dbp 2013-10-30): No subtyping - cases type
                    # must match constructors exactly.
                    if ret <> type:
                      ty-ers.add-error(branch.l,
                        msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                        )
                    else if args.length() <> branch.args.length():
                      ty-ers.add-error(branch.l,
                            msg(errCasesPatternNumberFields,
                              [branch.name, args.length(), branch.args.length()])
                            )
                    else:
                      # NOTE(dbp 2013-10-30): We want to check that
                      # branches have the same type.  This is slightly
                      # tricky, so we'll opt for a temporary but dynless solution -
                      # set it to the first branches type, and make
                      # sure all the rest are equal.
                      branchenv = env +
                          for map2(bind from branch.args,
                                   argty from args):
                            pair(bind.id, argty)
                          end
                      branchty = tc(branch.body, iifs, branchenv, type-env)
                      if ty-ers.type == dynType: # in first branch
                        branchty.merge-messages(ty-ers) # set branchty's type
                      else:
                        if branchty.type == ty-ers.type:
                          ty-ers.merge-messages(branchty)
                        else:
                          ty-ers.merge-messages(branchty).add-error(branch.l,
                            msg(errCasesBranchType, [branch.name])
                            )
                        end
                      end
                    end
                  | baseType(_,_) =>
                    if ty <> type:
                      ty-ers.add-error(branch.l,
                        msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                        )
                    else:
                      branchty = tc-curried(branch.body)
                      if ty-ers.type == dynType:
                        branchty.merge-messages(ty-ers)
                      else:
                        if branchty.type == ty-ers.type:
                          ty-ers.merge-messages(branchty)
                        else:
                          ty-ers.merge-messages(branchty).add-error(branch.l,
                            msg(errCasesBranchType, [branch.name])
                            )
                        end
                      end
                    end
                  | else =>
                    ty-ers.add-error(branch.l,
                      msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                      )
                end
            end
          end, dynR)
      end
    | else => raise("tc: no case matched for: " + torepr(ast))
  end
end


################################################################################
# Testing harness helpers.                                                     #
################################################################################

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


################################################################################
# Testing harness commandline driver.                                          #
################################################################################

var files = []
baseR = Racket("racket/base")
cmdlineargs = baseR("current-command-line-arguments")
fun usage():
  print("Usage:\n
   raco pyret tc.arr tests (runs all tests)\n
   raco pyret tc.arr file.arr (runs single file)\n\n(running basic unit tests)\n")
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
        # NOTE(dbp 2013-09-29): We run the .arr file. It expects to
        # have a corresponding .err file.  if .err is non-empty, we
        # expect to see an error that matches the content of that
        # file. If it is empty, we expect it to produce nothing as the
        # output of type checking.
        stripped = strip-ext(path)
        print("Running " + stripped)
        errpath = stripped + ".err"
        code = F.input-file(path).read-file()
        err = F.input-file(errpath).read-file()
        if err.length() <> 0:
          err-msg = tc-file(path, code).format-errors()
          pair(path,pair(err-msg, err-msg.contains(err)))
          is pair(path, pair(err-msg, true))
        else:
          err-msg = tc-file(path, code).format-errors()
          pair(path, pair(err-msg,
              err-msg.contains("No type errors detected.")))
          is pair(path,pair(err-msg, true))
        end
      end
    end)
  end
end
