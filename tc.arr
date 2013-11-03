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
fun <V> Set-(o): List(o) end

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



#####################################################################
#                                                                   #
#     This is a big State Monad, so we can thread all the stuff.    #
#                                                                   #
#####################################################################

data TCSTate:
  | tcst(value, errors, iifs, env, type-env)
end
# NOTE(dbp 2013-11-02): The type we want is a parametric alias for an S -> Pair<V,S> function.
TCST = Function
fun return(v):
  fun(er,i,e,t): tcst(v,er,i,e,t) end
end
fun bind(mv, mf):
  fun(er,i,e,t):
    p = mv(er,i,e,t)
    mf(p.value)(p.errors,p.iifs,p.env,p.type-env)
  end
end
fun seq(mv1, mv2):
  bind(mv1, fun(_): mv2 end)
end
fun sequence(mvs):
  mvs.foldr(fun(m, mbase):
      bind(mbase, fun(base):
          bind(m, fun(v):
              return(link(v, base))
            end)
        end)
    end, return([]))
end
fun foldm(fn, base, lst):
  cases(List) lst:
    | empty => return(base)
    | link(f,r) => fn(base, f)^bind(fun(v): foldm(fn, v, r) end)
  end
end

fun get-errors():
  fun(er,i,e,t):
    tcst(er,er,i,e,t)
  end
end
fun get-iifs():
  fun(er,i,e,t):
    tcst(i,er,i,e,t)
  end
end
fun get-env():
  fun(er,i,e,t):
    tcst(e,er,i,e,t)
  end
end
fun get-type-env():
  fun(er,i,e,t):
    tcst(t,er,i,e,t)
  end
end
fun put-errors(errors):
  fun(er,i,e,t):
    tcst(nothing,errors,i,e,t)
  end
end
fun put-iifs(iifs):
  fun(er,i,e,t):
    tcst(nothing,er,iifs,e,t)
  end
end
fun put-env(env):
  fun(er,i,e,t):
    tcst(nothing,er,i,env,t)
  end
end
fun put-type-env(type-env):
  fun(er,i,e,t):
    tcst(nothing,er,i,e,type-env)
  end
end
fun run(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env)
end
fun eval(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env).value
end
fun exec-errors(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env).errors
end
fun exec-iifs(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env).iifs
end
fun exec-env(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env).type-env
end
fun exec-type-env(st-prog, errs, iifs, env, type-env):
  st-prog(errs,iifs,env,type-env).type-env
end

# NOTE(dbp 2013-11-01): Errors and iifs are threaded, envs are NOT.
fun add-error(l,e):
  doc: "adds an error to the threaded state"
  get-errors()^bind(fun(errors): put-errors(errors + [pair(l,e)]) end)
end
fun add-iif(name, type):
  doc: "adds an inferred function to the threaded state"
  get-iifs()^bind(fun(iifs): put-iifs([pair(name, type)] + iifs) end)
end
fun add-bindings(binds, mv):
  doc: "adds bindings to the env, in the context of a monadic value"
  get-env()^bind(fun(old-env):
      put-env(binds + old-env)^seq(
        mv^bind(fun(val):
            put-env(old-env)^seq(
              return(val))
          end))
    end)
end
fun add-type(name, mv):
  doc: "adds a type to the type-env, in the context of a monadic value"
  get-type-env()^bind(fun(old-env):
      put-type-env([name] + old-env)^seq(
        mv^bind(fun(val):
            put-type-env(old-env)^seq(
              return(val))
          end))
    end)
end


check:
  eval(
    add-error("l1", "error 1")^seq(add-error("l2", "error 2"))
      ^seq(return("hello")),
    [], [], [], []
    ) is "hello"
  exec-errors(
    add-error("l1", "error 1")^seq(add-error("l2", "error 2"))
      ^seq(return("hello")),
    [], [], [], []
    ) is [pair("l1","error 1"), pair("l2","error 2")]
  exec-env(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], []
    ) is []
  eval(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], []
    ) is [pair("a", "T")]
end

# # NOTE(dbp 2013-10-30): env included for debugging / tooling. It
# # should never be used for typechecking.
# data TCResult:
#   | tcResult(type :: Type, errors :: List<TypeError>, env, type-env) with:
#     set-type(self, ty :: Type):
#       tcResult(ty, self.errors, self.env, self.type-env)
#     end,
#     add-error(self, l :: Loc, er :: String):
#       tcResult(self.type, self.errors + [typeError(l,er)], self.env, self.type-env)
#     end,
#     merge-messages(self, other :: TCResult):
#       tcResult(self.type, self.errors + other.errors, self.env, self.type-env)
#     end
# sharing:
#   format-errors(self):
#     if (self.errors.length() == 0):
#       "No type errors detected."
#     else:
#       "Errors:\n" + torepr(self.errors)
#     end
#   end
# end


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

fun <V> set-get(s :: Set-<V>, v :: V) -> Bool:
  cases(List) s:
    | empty => false
    | link(f, r) => (v == f) or set-get(r, v)
  end
where:
  set-get(["a", "b", "c"], "a") is true
  set-get(["a", "b", "c"], "aa") is false
  set-get([], []) is false
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

fun get-type(ann :: A.Ann) -> TCST<Type>:
  cases(A.Ann) ann:
    | a_blank => return(dynType)
    | a_any => return(dynType)
    | a_name(l, id) =>
      get-type-env()^bind(fun(type-env):
          if set-get(type-env, id):
            return(nmty(id))
          else:
            add-error(l, msg(errTypeNotDefined, [fmty(nmty(id))]))^seq(
              return(dynType))
          end
        end)
    | a_arrow(l, args, ret) =>
      get-type(ret)^bind(fun(retty):
          sequence(args.map(get-type))^bind(fun(argsty):
              return(arrowType(argsty, retty, moreRecord([])))
            end)
        end)
    | a_record(l, fields) =>
      sequence(fields.map(
          fun(field):
            get-type(field.ann)^bind(
              fun(t): return(pair(field.name, t)) end)
          end))^bind(
        fun(fieldsty):
          return(baseType(
              topTag,
              normalRecord(fieldsty)))
        end)
    | else => return(dynType)
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

fun get-bindings(ast :: A.Expr) -> TCST<List<Pair<String, Type>>>:
  doc: "This function implements letrec behavior."
  anyty = baseType(topTag, moreRecord([]))
  fun name-val-binds(name, val):
    if A.is-a_blank(name.ann):
      tc(val)^bind(fun(ty): return([pair(name.id, ty)]) end)
    else:
      get-type(name.ann)^bind(fun(ty): return([pair(name.id, ty)]) end)
    end
  end
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      get-env()^bind(fun(start-env):
          for foldm(cur from start-env, stmt from stmts):
            get-bindings(stmt)^bind(fun(new-binds): put-env(new-binds + cur)^seq(return(new-binds + cur)) end)
          end
        end)
    | s_user_block(l, block) => get-bindings(block)
      # NOTE(dbp 2013-10-16): Use the ann if it exists, otherwise the type of value.
    | s_var(l, name, val) => name-val-binds(name, val)
    | s_let(l, name, val) => name-val-binds(name, val)
      # NOTE(dbp 2013-11-01): Not including, as bindings inside ifs shouldn't escape
    # | s_if(l, branches) =>
    #   # NOTE(dbp 2013-10-16): Adds a bunch of copies of env... woops
    #   branches.map(get-bindings(_,envs)).foldl(
    #     fun(binds, base): base.chain((_+_), binds) end, envs
    #     )
    | s_datatype(l, name, params, variants, _) =>
      sequence(variants.map(get-variant-bindings(name)))^bind(fun(vbs):
         return(vbs^concat() + [pair(name, arrowType([anyty], nmty("Bool"), moreRecord([])))])
        end)
    | else => return([])
  end
where:
  fun gb-src(src):
    eval(get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).post-desugar.block), [], [], [], default-type-env)
  end
  gb-src("x = 2") is [pair("x", nmty("Number"))]
  gb-src("x = 2 y = x") is [ pair("y", nmty("Number")),
                             pair("x", nmty("Number"))
                           ]
end

fun get-variant-bindings(tname :: String, variant :: A.Variant(fun(v):
                                     A.is-s_datatype_variant(v) or
                                     A.is-s_datatype_singleton_variant(v) end)) ->
    TCST<List<Pair<String, Type>>>:
  bigty = baseType(baseTag(tname), moreRecord([]))
  anyty = baseType(topTag, moreRecord([]))
  boolty = baseType(baseTag("Bool"), moreRecord([]))
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
    | s_datatype_variant(l, vname, members, constr) =>
      sequence(members.map(get-member-type))^bind(fun(memtys):
          return([pair(vname, arrowType(memtys, bigty, moreRecord([]))),
              pair("is-" + vname, arrowType([anyty], boolty, moreRecord([])))])
        end)
    | s_datatype_singleton_variant(l, vname, constr) =>
      return([pair(vname, bigty),
          pair("is-" + vname, arrowType([anyty], boolty, moreRecord([])))])
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
  eval(get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [], default-type-env)
  is
  [pair("foo", arrowType([], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]

  eval(get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", arrowType([strty], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]


  eval(get-variant-bindings("Foo",
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", arrowType([strty, boolty], footy, moreRecord([]))),
  pair("is-foo", arrowType([anyty], boolty, moreRecord([])))]
end


################################################################################
# is-inference: inferring types from the way they are used in check-blocks.    #
################################################################################

fun is-inferred-functions(ast :: A.Expr) -> TCST<List<Pair<String, Type>>>:
  fun find-is-pairs(name :: String, e :: A.Expr) -> TCST<List<Type>>:
    cases(A.Expr) e:
      | s_block(l, stmts) => sequence(stmts.map(find-is-pairs(name, _)))^bind(fun(ps): return(concat(ps)) end)
      | s_check_test(l, op, left, right) =>
        if op == "opis":
          # NOTE(dbp 2013-10-21): Really simple for now - only if it
          # is of form funname(args) is bar.
          cases(A.Expr) left:
            | s_app(l1, fn, args) =>
              cases(A.Expr) fn:
                | s_id(l2, fname) =>
                  if fname == name:
                    tc(right)^bind(fun(rightty):
                        sequence(args.map(tc))^bind(fun(argsty):
                            return([arrowType(argsty, rightty, moreRecord([]))])
                          end)
                      end)
                  else:
                    return([])
                  end
                | else => return([])
              end
            | else => return([])
          end
        else:
          return([])
        end
      | else => return([])
    end
  end
  cases(A.Expr) ast:
    | s_block(l, stmts) => sequence(stmts.map(is-inferred-functions))^bind(fun(fs): return(concat(fs)) end)
    | s_fun(l, name, params, args, ann, doc, body, ck) =>
      find-is-pairs(name, ck)^bind(fun(pairs):
          # NOTE(dbp 2013-10-21): this should do an least upper bound.
          if pairs <> []:
            return([pair(name, pairs.first)])
          else:
            return([])
          end
        end)
    | else => return([])
  end
where:
  fun iif-src(src):
    stx = A.parse(src,"anonymous-file", { ["check"]: false}).pre-desugar
    eval(is-inferred-functions(stx.block), [], [], [], default-type-env)
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
  iifs = exec-iifs(is-inferred-functions(stx.pre-desugar.block), [], [], env, default-type-env)
  resultty = exec-errors(tc-prog(stx.with-types), [], iifs, env, default-type-env)
  # print(resultty.env.map(torepr).join-str("\n"))
  resultty
end

fun tc-prog(prog :: A.Program) -> TCST<Type>:
  tc(prog.block)
end

fun tc-member(ast :: A.Member) -> TCST<Option<Pair<String,Type>>>:
  cases(A.Member) ast:
    | s_data_field(l, name, value) =>
      # NOTE(dbp 2013-10-14): This is a bummer, but if it isn't
      # immediately obviously a string, not sure what to do.
      cases(A.Expr) name:
        | s_str(l1, s) => tc(value)^bind(fun(ty): return(some(pair(s, ty))) end)
        | else => return(none)
      end
    | else => return(none)
    # | s_mutable_field(l, name, ann, value)
    # | s_once_field(l, name, ann, value)
    # | s_method_field(
  end
end


################################################################################
# Main typechecking function.                                                  #
################################################################################

fun tc(ast :: A.Expr) -> TCST<Type>:
  get-bindings(ast)^bind(fun(bindings):
      add-bindings(bindings,
        cases(A.Expr) ast:
          | s_block(l, stmts) => sequence(stmts.map(tc))^bind(
              fun(tys):
                return(if tys == []: nmty("Nothing") else: tys.last() end)
              end)
          | s_user_block(l, block) => tc(block)
          | s_var(l, name, val) => return(dynType)
          | s_let(l, name, val) =>
            # NOTE(dbp 2013-10-21): Ugly hack. We want to find
            # desugared funs, so we look for let bindings. Our no-shadowing
            # rule actually makes this easier, because since the iifs are
            # all top level, if we find a binding anywhere that has that
            # name, it must be the function.
            get-type(name.ann)^bind(fun(bindty):
                get-iifs()^bind(fun(iifs):
                    cases(option.Option) map-get(iifs, name.id):
                      | none =>
                        tc(val)^bind(fun(ty):
                            if not subtype(ty, bindty):
                              add-error(l, msg(errAssignWrongType,
                                  [name.id, fmty(bindty), fmty(ty.type)]))^seq(
                                return(dynType))
                            else:
                              return(ty)
                            end
                          end)
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
                            sequence(for map2(b from args, inf from fty.args):
                                if A.is-a_blank(b.ann):
                                  when inf <> dynType:
                                    inferred := true
                                  end
                                  return(inf)
                                else:
                                  get-type(b.ann)
                                end
                              end)^bind(fun(arg-tys):
                                add-bindings(for map2(b from args, t from arg-tys):
                                    pair(b.id, t)
                                  end,
                                  tc(body)^bind(fun(body-ty):
                                      (if A.is-a_blank(ann): return(fty.ret) else: get-type(ann) end)^bind(fun(ret-ty):
                                          if subtype(body-ty, ret-ty):
                                            return(arrowType(arg-tys, ret-ty, moreRecord([])))
                                          else:
                                            add-error(l,
                                              if inferred:
                                                msg(errFunctionInferredIncompatibleReturn,
                                                  [fmty(body-ty), fmty(ret-ty)])
                                              else:
                                                msg(errFunctionAnnIncompatibleReturn,
                                                  [fmty(body-ty), fmty(ret-ty)])
                                              end)^seq(return(dynType))
                                          end
                                        end)
                                    end)
                                  )
                              end)
                          | else =>
                            # NOTE(dbp 2013-10-21): This is a bizarre case. It means
                            # we no longer understand the desugaring, so we really
                            # should abort and figure our stuff out.
                            raise("Type Checker error: encountered a let binding that
                              should have been a function, but wasn't (at loc " +
                              torepr(l) + ")")
                        end
                    end
                  end)
              end)
          | s_assign(l, id, val) => return(dynType)
          | s_if(l, branches) => return(dynType)
          | s_lam(l, ps, args, ann, doc, body, ck) =>
            get-type(ann)^bind(fun(ret-ty):
                sequence(args.map(fun(b): get-type(b.ann)^bind(fun(t): return(pair(b.id, t)) end) end))^bind(fun(new-binds):
                    add-bindings(new-binds,
                      tc(body)^bind(fun(body-ty):
                          if subtype(body-ty, ret-ty):
                            return(arrowType(new-binds.map(fun(bnd): bnd.b end), ret-ty, moreRecord([])))
                          else:
                            add-error(l,
                              msg(errFunctionAnnIncompatibleReturn,
                                [fmty(body-ty), fmty(ret-ty)]))^seq(
                              return(dynType))
                          end
                        end)
                      )
                  end)
              end)
          | s_method(l, args, ann, doc, body, ck) => return(dynType)
          | s_extend(l, super, fields) =>
            tc(super)^bind(fun(base):
                for foldm(ty from base, fld from fields):
                  tc-member(fld)^bind(fun(mty):
                      cases(Option) mty:
                        | none => return(ty)
                        | some(fldty) =>
                          return(type-record-add(ty, fldty.a, fldty.b))
                      end
                    end)
                end
              end)
          | s_update(l, super, fields) => return(dynType)
          | s_obj(l, fields) =>
            (for foldm(acc from normalRecord([]), f from fields):
                tc-member(f)^bind(fun(mty):
                    cases(option.Option) mty:
                      | none =>
                        return(moreRecord(acc.fields))
                        # NOTE(dbp 2013-10-16): This is a little bit of a hack -
                        # to reuse the helper that wants to operate on types.
                      | some(fty) =>
                        return(type-record-add(baseType(topTag,acc), fty.a, fty.b).record)
                    end
                  end)
              end)^bind(fun(record):
                return(baseType(botTag, record))
              end)
          | s_app(l, fn, args) =>
            tc(fn)^bind(fun(fn-ty):
                cases(Type) fn-ty:
                  | arrowType(arg-types, ret-type, rec-type) =>
                    if args.length() <> arg-types.length():
                      add-error(l,
                        msg(errArityMismatch, [arg-types.length(), args.length()]))^seq(
                        return(dynType))
                    else:
                      sequence(args.map(tc))^bind(fun(arg-vals):
                          var counter = 1
                          var arg-error = false
                          sequence(
                            for map2(at from arg-types, av from arg-vals):
                              if not subtype(av, at):
                                arg-error := true
                                add-error(l,
                                  msg(errArgumentBadType, [counter, fmty(at), fmty(av.type)]))
                              else:
                                return(nothing)
                              end
                            end)^seq(return(if arg-error: dynType else: ret-type end))
                        end)
                    end
                    # NOTE(dbp 2013-10-16): Not really anything we can do. Odd, but...
                  | dynType => return(dynType)
                  | else =>
                    add-error(l, msg(errApplyNonFunction, [fmty(fn-ty)]))^seq(return(dynType))
                end
              end)
          | s_id(l, id) =>
            get-env()^bind(fun(env):
                cases(option.Option) map-get(env, id):
                  | none => add-error(l, msg(errUnboundIdentifier, [id]))^seq(return(dynType))
                  | some(ty) => return(ty)
                end
              end)
          | s_num(l, num) => return(nmty("Number"))
          | s_bool(l, bool) => return(nmty("Bool"))
          | s_str(l, str) => return(nmty("String"))
          | s_get_bang(l, obj, str) => return(dynType)
          | s_bracket(l, obj, field) =>
            cases(A.Expr) field:
              | s_str(l1, s) =>
                tc(obj)^bind(fun(obj-ty):
                    cases(Type) obj-ty:
                      | dynType => return(dynType)
                      | else =>
                        cases(RecordType) obj-ty.record:
                          | normalRecord(fields) =>
                            cases(Option) map-get(fields, s):
                              | none => add-error(l, msg(errFieldNotFound, [s]))^seq(return(dynType))
                              | some(ty) => return(ty)
                            end
                          | moreRecord(fields) =>
                            cases(Option) map-get(fields, s):
                              | none => return(dynType)
                              | some(ty) => return(ty)
                            end
                        end
                    end
                  end)
              | else =>
                # NOTE(dbp 2013-10-21): Actually type check field to see if
                # it is a String or Dyn
                return(dynType)
            end
          | s_colon_bracket(l, obj, field) => return(dynType)
          | s_datatype(l, name, params, variants, check) =>
            # NOTE(dbp 2013-10-30): Should statements have type nothing?
            return(nmty("Nothing"))
          | s_cases(l, _type, val, branches) =>
            get-type(_type)^bind(
              fun(type):
                tc(val)^bind(
                  fun(val-ty):
                    if not subtype(type, val-ty):
                      add-error(l,
                        msg(errCasesValueBadType, [fmty(type), fmty(val-ty.type)])
                        )^seq(return(dynType))
                    else:
                      get-env()^bind(
                        fun(env):
                          var branches-ty = dynType
                          sequence(branches.map(fun(branch):
                                # TODO(dbp 2013-10-30): Need to have a data-env, so we can
                                # pick up non-bound constructors.
                                cases(Option) map-get(env, branch.name):
                                  | none => add-error(branch.l,
                                      msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                                      )
                                  | some(ty) =>
                                    cases(Type) ty:
                                      | arrowType(args, ret, rec) =>
                                        # NOTE(dbp 2013-10-30): No subtyping - cases type
                                        # must match constructors exactly.
                                        if ret <> type:
                                          add-error(branch.l,
                                            msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                                            )
                                        else if args.length() <> branch.args.length():
                                          add-error(branch.l,
                                            msg(errCasesPatternNumberFields,
                                              [branch.name, args.length(), branch.args.length()])
                                            )
                                        else:
                                          # NOTE(dbp 2013-10-30): We want to check that
                                          # branches have the same type.  This is slightly
                                          # tricky, so we'll opt for a temporary but dynless solution -
                                          # set it to the first branches type, and make
                                          # sure all the rest are equal.
                                          add-bindings(for map2(bnd from branch.args,
                                                argty from args):
                                              pair(bnd.id, argty)
                                            end,
                                            tc(branch.body)^bind(fun(branchty):
                                                if branches-ty == dynType: # in first branch
                                                  branches-ty := branchty
                                                  return(branchty)
                                                else:
                                                  if branchty == branches-ty:
                                                    return(branchty)
                                                  else:
                                                    add-error(branch.l,
                                                      msg(errCasesBranchType, [branch.name])
                                                      ).seq(return(branches-ty))
                                                  end
                                                end
                                              end))
                                        end
                                      | baseType(_,_) =>
                                        if ty <> type:
                                          add-error(branch.l,
                                            msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                                            ).seq(return(dynType))
                                        else:
                                          tc(branch.body)^bind(fun(branchty):
                                              if branches-ty == dynType:
                                                branches-ty := branchty
                                                return(branchty)
                                              else:
                                                if branchty == branches-ty:
                                                  return(branchty)
                                                else:
                                                  add-error(branch.l,
                                                    msg(errCasesBranchType, [branch.name])
                                                    ).seq(return(branches-ty))
                                                end
                                              end
                                            end)
                                        end
                                      | else =>
                                        add-error(branch.l,
                                          msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                                          )^seq(dynType)
                                    end
                                end
                              end))
                        end)
                    end
                  end)
              end)
          | else => raise("tc: no case matched for: " + torepr(ast))
        end
        )
    end
    )
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
          err-msg = tc-file(path, code).map(torepr).join-str("\n")
          pair(path,pair(err-msg, err-msg.contains(err)))
          is pair(path, pair(err-msg, true))
        else:
          err-msg = tc-file(path, code).map(torepr).join-str("\n")
          pair(path, pair(err-msg,
              err-msg.contains("No type errors detected.")))
          is pair(path,pair(err-msg, true))
        end
      end
    end)
  end
end
