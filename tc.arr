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
  end
end

data TypeError:
  | typeError(location :: Loc, message :: String)
end

data Type:
  | dynType
  | baseType(tag :: TagType, record :: RecordType)
  | arrowType(params :: List<String>, args :: List<Type>, ret :: Type, record :: RecordType)
  | methodType(params :: List<String>, self :: Type, args :: List<Type>, ret :: Type, record :: RecordType)
sharing:
  _equals(self, other):
    cases(Type) self:
      | dynType => is-dynType(other)
      | baseType(tag, record) =>
        is-baseType(other) and (tag == other.tag) and (record == other.record)
      | arrowType(params, args, ret, record) =>
        is-arrowType(other) and (params == other.params) and (args == other.args)
        and (ret == other.ret) and (record == other.record)
      | methodType(params, mself, args, ret, record) =>
        is-methodType(other) and (params == other.params) and (mself == other.self)
        and (args == other.args)
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

data TCstate:
  | tcst(
      value,
      errors :: List<TypeError>,
      iifs :: List<Pair<String, Type>>,
      env :: List<Pair<String, Type>>,
      type-env :: List<Pair<String, Type>>
      )
end

# NOTE(dbp 2013-11-02): The type we want is a parametric alias for an
# S -> Pair<V,S> function, where S is (errors, iifs, env, type-env)
TCST = Function

# First the fundamental monad functions
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

# Next the common monad helpers
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

# After that, the state-related functions
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

# And finally, application specific actions (note that errors are
# threaded, binds and types are not.)
fun add-error(l,e):
  doc: "adds an error to the threaded state"
  get-errors()^bind(fun(errors): put-errors(errors + [pair(l,e)]) end)
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
fun add-types(binds, mv):
  doc: "adds types to the type-env, in the context of a monadic value"
  get-type-env()^bind(fun(old-type-env):
      put-type-env(binds + old-type-env)^seq(
        mv^bind(fun(val):
            put-type-env(old-type-env)^seq(
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
  | errUnknownTypeParameter with: tostring(self):
      "The return type was a type parameter that did not
      appear in the argument list."
    end
end

fun msg(err :: TCError, values :: List<Any>) -> String:
  tostring(err) +
  "\n\nRelated values:\n\n" + values.map(tostring).join-str(", ") + "\n"
end

fun fmty(type :: Type) -> String:
  fun fmfields(fields):
    fields.map(fun(p): p.a + " : " + fmty(p.b) end).join-str(", ")
  end
  fun fmarrow(params, args, ret):
    if params == []: "" else: "<" + params.join-str(", ") + ">" end +
    "(" + args.map(fmty).join-str(", ") + " -> " + fmty(ret) + ")"
  end
  cases(Type) type:
    | dynType => "Dyn*"
    | baseType(tag, rec) =>
      cases(TagType) tag:
        | baseTag(nm) => nm
        | topTag => "Any*"
        | botTag =>
          cases(RecordType) rec:
            | normalRecord(fields) =>
              "{" + fmfields(fields) + "}"
            | moreRecord(fields) =>
              "{" + fmfields(fields) + "...}"
          end
      end
    | arrowType(params, args, ret, rec) => fmarrow(params, args, ret)
    | methodType(params, self, args, ret, rec) => fmarrow(params, [self]+args, ret)
  end
end

fun pretty-error(ep :: Pair<Loc, String>) -> String:
  "Line " + tostring(ep.a.line) + ", Column " + tostring(ep.a.column) + " - " + ep.b
end

fun pretty-iif(iif :: Pair<String, Type>) -> String:
  "fun " + iif.a + " :: " + fmty(iif.b)
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

fun tyequal(t1 :: Type, t2 :: Type) -> Bool:
  doc: "Type equality, allowing for moreRecords containing unknown additional fields."
  fun recequal(r1 :: RecordType, r2 :: RecordType) -> Bool:
    doc: "Everything mentioned in a moreRecord must be in the normalRecord."
    cases(RecordType) r1:
      | normalRecord(fields1) =>
        cases(RecordType) r2:
          | normalRecord(fields2) => fields1 == fields2
          | moreRecord(fields2) =>
            for fold(base from true, field from fields2):
              base and fields1.member(field)
            end
        end
      | moreRecord(fields1) =>
        cases(RecordType) r2:
          | normalRecord(fields2) =>
            for fold(base from true, field from fields1):
              base and fields2.member(field)
            end
          | moreRecord(_) => true
        end
    end
  end
  cases(Type) t1:
    | baseType(tag1, rec1) =>
      cases(Type) t2:
        | baseType(tag2, rec2) =>
          (tag1 == tag2) and recequal(rec1, rec2)
        | else => false
      end
    | arrowType(params1, args1, ret1, rec1) =>
      cases(Type) t2:
        | arrowType(params2, args2, ret2, rec2) =>
          (params1 == params2) and (args1 == args2) and (ret1 == ret2) and recequal(rec1, rec2)
        | else => false
      end
    | methodType(params1, self1, args1, ret1, rec1) =>
      cases(Type) t2:
        | methodType(params2, self2, args2, ret2, rec2) =>
          (params1 == params2) and (self1 == self2) and (args1 == args2) and (ret1 == ret2) and recequal(rec1, rec2)
        | else => false
      end
    | dynType => t2 == dynType
  end
where:
  tyequal(nmty("A"), nmty("A")) is true
  tyequal(nmty("A"), nmty("B")) is false
  tyequal(nmty("A"), baseType(baseTag("A"), moreRecord([pair("b", nmty("Number"))]))) is true
  tyequal(baseType(baseTag("A"), normalRecord([])), baseType(baseTag("A"), moreRecord([pair("b", nmty("Number"))]))) is false
  tyequal(baseType(baseTag("A"), normalRecord([])), baseType(baseTag("A"), normalRecord([]))) is true
  tyequal(baseType(baseTag("A"), normalRecord([])), baseType(baseTag("A"), normalRecord([pair("b", nmty("Number"))]))) is false
  tyequal(nmty("A"), arrowType([], [], nmty("A"), moreRecord([]))) is false
  tyequal(arrowType([],[], nmty("A"), moreRecord([pair("b", nmty("Number"))])), arrowType([],[], nmty("A"), moreRecord([]))) is true
  tyequal(arrowType([],[], nmty("A"), normalRecord([pair("b", nmty("Number"))])), arrowType([],[], nmty("A"), moreRecord([]))) is true
  tyequal(arrowType([],[], nmty("A"), normalRecord([pair("b", nmty("Number"))])), arrowType([],[], nmty("A"), normalRecord([]))) is false
  tyequal(arrowType([],[], nmty("A"), normalRecord([])), arrowType([],[], nmty("A"), moreRecord([pair("b", nmty("Number"))]))) is false
end

fun get-type(ann :: A.Ann) -> TCST<Type>:
  cases(A.Ann) ann:
    | a_blank => return(dynType)
    | a_any => return(baseType(topTag, moreRecord([])))
    | a_name(l, id) =>
      get-type-env()^bind(fun(type-env):
          cases(Option) map-get(type-env, id):
            | some(ty) => return(ty)
            | none =>
              add-error(l, msg(errTypeNotDefined, [fmty(nmty(id))]))^seq(
                return(dynType))
          end
        end)
    | a_arrow(l, args, ret) =>
      get-type(ret)^bind(fun(retty):
          sequence(args.map(get-type))^bind(fun(argsty):
              return(arrowType([],argsty, retty, moreRecord([])))
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
    | else => raise("type-record-add: didn't match " + torepr(orig))
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
      # NOTE(dbp 2013-11-03): Giving the id dyn seems wrong... but
      # also not sure what else to do, as we need some type for
      # desugared recursive functions.
      add-bindings([pair(name.id, dynType)],
        tc(val)^bind(fun(ty): return([pair(name.id, ty)]) end))
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
      add-types(params.map(fun(n): pair(n, nmty(n)) end),
        sequence(variants.map(get-variant-bindings(name, params, _)))^bind(fun(vbs):
            return(vbs^concat() + [pair(name, arrowType(params, [anyty], nmty("Bool"), moreRecord([])))])
          end)
        )
    | else => return([])
  end
where:
  fun gb-src(src):
    eval(get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], default-type-env)
  end
  gb-src("x = 2") is [pair("x", nmty("Number"))]
  gb-src("x = 2 y = x") is [ pair("y", nmty("Number")),
                             pair("x", nmty("Number"))
                           ]
end

fun get-variant-bindings(tname :: String, tparams :: List<String>, variant :: A.Variant(fun(v):
                                     A.is-s_datatype_variant(v) or
                                     A.is-s_datatype_singleton_variant(v) end)) ->
    TCST<List<Pair<String, Type>>>:
  bigty = nmty(tname)
  anyty = baseType(topTag, moreRecord([]))
  boolty = nmty("Bool")
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
    | s_datatype_variant(l, vname, members, constr) =>
      sequence(members.map(get-member-type))^bind(fun(memtys):
          return([pair(vname, arrowType(tparams, memtys, bigty, moreRecord([]))),
              pair("is-" + vname, arrowType([],[anyty], boolty, moreRecord([])))])
        end)
    | s_datatype_singleton_variant(l, vname, constr) =>
      return([pair(vname, bigty),
          pair("is-" + vname, arrowType([],[anyty], boolty, moreRecord([])))])
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
  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [], default-type-env)
  is
  [pair("foo", arrowType([],[], footy, moreRecord([]))),
    pair("is-foo", arrowType([],[anyty], boolty, moreRecord([])))]

  eval(get-variant-bindings("Foo", ["T"],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", arrowType(["T"],[strty], footy, moreRecord([]))),
    pair("is-foo", arrowType([],[anyty], boolty, moreRecord([])))]


  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", arrowType([],[strty, boolty], footy, moreRecord([]))),
    pair("is-foo", arrowType([],[anyty], boolty, moreRecord([])))]
end

fun get-type-bindings(ast :: A.Expr) -> TCST<List<Pair<String>>>:
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      sequence(stmts.map(get-type-bindings))^bind(fun(bs): return(concat(bs)) end)
    | s_user_block(l, block) => get-type-bindings(block)
    | s_datatype(l, name, _, _, _) =>
      return([pair(name, nmty(name))])
    | else => return([])
  end
where:
  fun gtb-src(src):
    eval(get-type-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [])
  end
  gtb-src("x = 2") is []
  gtb-src("datatype Foo: | foo with constructor(self): self end end") is [pair("Foo", nmty("Foo"))]
  gtb-src("datatype Foo: | foo with constructor(self): self end end
           datatype Bar: | bar with constructor(self): self end end") is
  [pair("Foo", nmty("Foo")), pair("Bar", nmty("Bar"))]
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
                            return([arrowType([],argsty, rightty, moreRecord([]))])
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
  [pair("f", arrowType([],[], nmty("Number"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end") is
    [pair("f", arrowType([],[nmty("String")], nmty("Bool"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: g() is 10 end") is
    [pair("f", arrowType([],[nmty("String")], nmty("Bool"), baseRec)),
    pair("g", arrowType([],[], nmty("Number"), baseRec))]
  iif-src("fun f(x): 10 where: f('foo') is true end
    fun g(): 10 where: f() is 10 end") is
  [pair("f", arrowType([],[nmty("String")], nmty("Bool"), baseRec))]
  iif-src("fun f(x): add1(x) where: f('Fo') is 10 end") is
  [pair("f", arrowType([],[nmty("String")], nmty("Number"), baseRec))]
end


################################################################################
# Subtyping.                                                                   #
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
    | arrowType(parentparams, parentargs, parentret, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | arrowType(childparams, childargs, childret, childrecord) =>
          # NOTE(dbp 2013-11-04): To do this correctly, probably need to canonically rename type params.
          for fold2(wt from (childargs.length() == parentargs.length())
                            and subtype(parentret, childret)
                            and (parentparams == childparams),
                    ct from childargs,
                    pt from parentargs):
            wt and subtype(ct, pt)
          end
        | else => false
      end
    | methodType(parentparams, parentself, parentargs, parentret, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | methodType(childparams, childself, childargs, childret, childrecord) =>
          for fold2(wt from (childargs.length() == parentargs.length())
                            and subtype(parentret, childret)
                            and subtype(childself, parentself)
                            and (parentparams == childparams),
              ct from childargs,
              pt from parentargs):
            wt and subtype(ct, pt)
          end
        | else => false
      end
    | baseType(parenttags, parentrecord) =>
      cases(Type) child:
        | dynType => true
        | baseType(childtags, childrecord) =>
          tag-subtype(childtags, parenttags) and
              record-subtype(childrecord, parentrecord)
        | else => false
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

  subtype(arrowType([],[], dynType, moreRecord([])),        arrowType([],[dynType], dynType, moreRecord([]))) is false
  subtype(arrowType([],[numType], dynType, moreRecord([])), arrowType([],[topType], dynType, moreRecord([]))) is true
  subtype(arrowType([],[topType], dynType, moreRecord([])), arrowType([],[numType], dynType, moreRecord([]))) is false
  subtype(arrowType([],[topType], dynType, moreRecord([])), arrowType([],[topType], dynType, moreRecord([]))) is true
  subtype(arrowType([],[topType], topType, moreRecord([])), arrowType([],[topType], numType, moreRecord([]))) is true
  subtype(arrowType([],[topType], numType, moreRecord([])), arrowType([],[topType], topType, moreRecord([]))) is false

  subtype(methodType([],dynType, [], dynType, moreRecord([])),
    methodType([],dynType, [dynType], dynType, moreRecord([]))) is false
  subtype(methodType([],numType, [topType], dynType, moreRecord([])),
    methodType([],topType, [topType], dynType, moreRecord([]))) is true
  subtype(methodType([],numType, [topType], dynType, moreRecord([])),
    methodType([],numType, [numType], dynType, moreRecord([]))) is false
  subtype(methodType([],topType, [topType], dynType, moreRecord([])),
    methodType([],topType, [topType], dynType, moreRecord([]))) is true
  subtype(methodType([],numType, [topType], topType, moreRecord([])),
    methodType([],topType, [topType], numType, moreRecord([]))) is true
  subtype(methodType([],numType, [topType], numType, moreRecord([])),
    methodType([],topType, [topType], topType, moreRecord([]))) is false
end


################################################################################
# tc Helper functions and builtin env and type-env                             #
################################################################################
top-type = baseType(topTag, moreRecord([]))
list-type = baseType(baseTag("List"), moreRecord([
      pair("length", methodType([],dynType, [], nmty("Number"), moreRecord([])))
    ]))
nothing-type = baseType(baseTag("Nothing"), normalRecord([]))

default-type-env = [
  pair("Any", top-type),
  pair("Bool",  baseType(baseTag("Bool"), moreRecord([]))),
  pair("Number", baseType(baseTag("Number"), moreRecord([]))),
  pair("String", baseType(baseTag("String"), moreRecord([]))),
  pair("List", list-type),
  pair("Nothing", nothing-type)
]

fun tc-main(p, s):
  env = [
    pair("Any", top-type),
    pair("list", baseType(botTag,
        moreRecord([
            pair("map", top-type),
            pair("link", arrowType([],[top-type, list-type], list-type, moreRecord([]))),
            pair("empty", list-type)
          ]))),
    pair("builtins", baseType(botTag,
        moreRecord([]))),
    pair("link", arrowType([],[dynType, dynType], list-type, moreRecord([]))),
    pair("empty", list-type),
    pair("nothing", nothing-type),
    pair("print", arrowType([], [top-type], nothing-type, moreRecord([])))
  ]
  stx = s^A.parse(p, { ["check"]: false})
  # NOTE(dbp 2013-11-03): This is sort of crummy. Need to get bindings first, for use
  # with inferring functions, but then will do this again when we start type checking...
  bindings = eval(get-bindings(stx.with-types.block), [], [], env, default-type-env)
  iifs = eval(is-inferred-functions(stx.pre-desugar.block), [], [], bindings + env, default-type-env)
  run(tc-prog(stx.with-types), [], iifs, env, default-type-env)
end

fun tc-file(p, s):
  tc-main(p,s).errors
end

fun tc-report(p, s):
  print("Report for " + p + ":\n\n")
  result = tc-main(p,s)
  if result.errors.length() <> 0:
    print("Errors detected:\n")
    print(result.errors.map(pretty-error).join-str("\n"))
  else:
    print("No type errors detected.")
  end
  when result.iifs.length() <> 0:
    print("\n\nTop level inferred functions:\n")
    print(result.iifs.map(pretty-iif).join-str("\n"))
  end
  print("\n")
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
  get-type-bindings(ast)^bind(fun(newtypes):
      add-types(newtypes,
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
                                        [name.id, fmty(bindty), fmty(ty)]))^seq(
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
                                                  return(arrowType(ps, arg-tys, ret-ty, moreRecord([])))
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
                  # NOTE(dbp 2013-11-03): Check for type shadowing.
                  add-types(ps.map(fun(n): pair(n, nmty(n)) end),
                    get-type(ann)^bind(fun(ret-ty):
                        sequence(args.map(fun(b): get-type(b.ann)^bind(fun(t): return(pair(b.id, t)) end) end))^bind(fun(new-binds):
                            add-bindings(new-binds,
                              tc(body)^bind(fun(body-ty):
                                  if subtype(body-ty, ret-ty):
                                    return(arrowType(ps, new-binds.map(fun(bnd): bnd.b end), ret-ty, moreRecord([])))
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
                    )
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
                        | arrowType(params, arg-types, ret-type, rec-type) =>
                          if args.length() <> arg-types.length():
                            add-error(l,
                              msg(errArityMismatch, [arg-types.length(), args.length()]))^seq(
                              return(dynType))
                          else:
                            sequence(args.map(tc))^bind(fun(arg-vals):
                                var counter = 1
                                var arg-error = false
                                var param-inst = []
                                sequence(
                                  for map2(at from arg-types, av from arg-vals):
                                    # NOTE(dbp 2013-11-04): If it is a type parameter, instantiate it greedily.
                                    if is-baseType(at) and is-baseTag(at.tag) and params.member(at.tag.name):
                                      cases(Option) map-get(param-inst, at):
                                        | none =>
                                          param-inst := link(pair(at, av), param-inst)
                                          return(nothing)
                                        | some(exist) =>
                                          if not tyequal(exist, av):
                                            arg-error := true
                                            add-error(l,
                                              msg(errArgumentBadType, [counter, fmty(at), fmty(av)]))
                                          else:
                                            return(nothing)
                                          end
                                      end
                                    else if not subtype(av, at):
                                      arg-error := true
                                      add-error(l,
                                        msg(errArgumentBadType, [counter, fmty(at), fmty(av)]))
                                    else:
                                      return(nothing)
                                    end
                                  end)^seq(block:
                                  if arg-error:
                                    return(dynType)
                                  else if is-baseType(ret-type) and is-baseTag(ret-type.tag) and params.member(ret-type.tag.name):
                                    cases(Option) map-get(param-inst, ret-type):
                                      | nothing =>
                                        # NOTE(dbp 2013-11-04): I don't actually think there is a way for this to happen...
                                        add-error(l,
                                          msg(errUnknownTypeParameter, [fmty(ret-type)])).seq(return(dynType))
                                      | some(t) => return(t)
                                    end
                                  else:
                                    return(ret-type)
                                  end
                                  end)
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
                  # NOTE(dbp 2013-11-03): We aren't actually checking methods, just applying them.
                  fun method-apply(ty):
                    cases(Type) ty:
                      | methodType(ps, self, args, ret, rec) =>
                        arrowType(ps, args, ret, rec)
                      | else => ty
                    end
                  end
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
                                    | some(ty) => return(method-apply(ty))
                                  end
                                | moreRecord(fields) =>
                                  cases(Option) map-get(fields, s):
                                    | none => return(dynType)
                                    | some(ty) => return(method-apply(ty))
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
                              msg(errCasesValueBadType, [fmty(type), fmty(val-ty)])
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
                                            | arrowType(params, args, ret, rec) =>
                                              # NOTE(dbp 2013-10-30): No subtyping - cases type
                                              # must match constructors exactly (modulo records)
                                              if not tyequal(ret, type):
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
                                                            )^seq(return(branches-ty))
                                                        end
                                                      end
                                                    end))
                                              end
                                            | baseType(_,_) =>
                                              if not tyequal(ty, type):
                                                add-error(branch.l,
                                                  msg(errCasesBranchInvalidVariant, [fmty(type), branch.name])
                                                  )^seq(return(dynType))
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
                                                          )^seq(return(branches-ty))
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
                                    end))^seq(return(branches-ty))
                              end)
                          end
                        end)
                    end)
                | else => raise("tc: no case matched for: " + torepr(ast))
              end
              )
          end
          )
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
cmdlineargs = baseR("vector->list", baseR("current-command-line-arguments"))
fun usage():
  print("Usage:\n
   raco pyret tc.arr tests (runs all tests)\n
   raco pyret tc.arr file.arr (runs single file)\n\n(running basic unit tests)\n")
end
fun format-errors(ers):
  cases(List) ers:
    | empty => "No type errors detected."
    | link(_,_) => ers.map(torepr).join-str("\n")
  end
end
if cmdlineargs.length() == 1:
  usage()
else:
  mode = cmdlineargs.get(1)
  if mode == "tests":
    files := D.dir("tests").list().map(fun(path): build-path(["tests", path]) end)
  # NOTE(dbp 2013-11-03): Really need a commandline parsing library...
  else if (mode == "report") or
    ((cmdlineargs.get(0) == "--no-checks") and (cmdlineargs.get(2) == "report")):
    path = cmdlineargs.get(if mode == "report": 2 else: 3 end)
    tc-report(path, F.input-file(path).read-file())
  else if baseR("file-exists?", mode):
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
          err-msg = format-errors(tc-file(path, code))
          pair(path,pair(err-msg, err-msg.contains(err)))
          is pair(path, pair(err-msg, true))
        else:
          err-msg = format-errors(tc-file(path, code))
          pair(path, pair(err-msg,
              err-msg.contains("No type errors detected.")))
          is pair(path,pair(err-msg, true))
        end
      end
    end)
  end
end
