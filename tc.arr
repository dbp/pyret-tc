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
    is-pair(other) and (self.a == other.a) and (self.b == other.b)
  end
end

data TypeError:
  | typeError(location :: Loc, message :: String)
end

data Type:
  | dynType
  | anyType
  | nameType(name :: String)
  | anonType(record :: RecordType)
  | arrowType(args :: List<Type>, ret :: Type, record :: RecordType)
  | methodType(self :: Type, args :: List<Type>, ret :: Type, record :: RecordType)
  | appType(name :: String, args :: List<Type>)
  | bigLamType(params :: List<String>, type :: Type)
sharing:
  _equals(self, other):
    cases(Type) self:
      | dynType => is-dynType(other)
      | anyType => is-anyType(other)
      | nameType(name) =>
        is-nameType(other) and (name == other.name)
      | anonType(record) =>
        is-anonType(other) and (record == other.record)
      | arrowType(args, ret, record) =>
        is-arrowType(other) and (args == other.args)
        and (ret == other.ret) and (record == other.record)
      | methodType(mself, args, ret, record) =>
        is-methodType(other) and (mself == other.self)
        and (args == other.args)
        and (ret == other.ret) and (record == other.record)
      | appType(name, args) =>
        is-appType(other) and (name == other.name)
        and (args == other.args)
      | bigLamType(params, type) =>
        is-bigLamType(other) and (self.type == other.type)
    end
  end
where:
  anyType == anyType is true
  nameType("Foo") == appType("Foo", []) is false
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

data TypeBinding:
  | typeAlias(type :: Type)
  | typeNominal(type :: Type)
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
      type-env :: List<Pair<String, TypeBinding>>
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
  | errAssignWrongType(id, bindty, valty) with: tostring(self):
      "The identifier " + self.id + " was defined to have type " + self.bindty + ", but assigned a value of an incompatible type: " + self.valty + "."
    end
  | errFunctionInferredIncompatibleReturn(bodyty, retty) with: tostring(self):
      "The body of the function has type " + self.bodyty + ", which is incompatible with the return type, " + self.retty + ", inferred based on tests."
    end
  | errFunctionAnnIncompatibleReturn(bodyty, retty) with: tostring(self):
      "The body of the function has type " + self.bodyty + ", which is incompatible with the return type specified in annotations as " + self.retty + "."
    end
  | errArityMismatch(expected, given) with: tostring(self):
      "Arity mismatch: function expected " + tostring(self.expected) + " arguments, but was passed " + tostring(self.given) + "."
    end
  | errArgumentBadType(position, expected, given) with: tostring(self):
      "The " + ordinalize(self.position) + " argument was expected to be of type " + self.expected + ", but was the incompatible type " + self.given + "."
    end
  | errApplyNonFunction(ty) with: tostring(self):
      "Applying a non-function value of type " + self.ty + "."
    end
  | errUnboundIdentifier(id) with: tostring(self):
      "Identifier " + self.id + " is unbound."
    end
  | errFieldNotFound(name) with: tostring(self):
      "Field " + self.name + " not present on object."
    end
  | errCasesValueBadType(expected, given) with: tostring(self):
      "The value in cases expression should have type " + self.expected + ", but has incompatible type " + self.given + "."
    end
  | errCasesBranchInvalidVariant(type, name) with: tostring(self):
      "The branch " + self.name + " in the cases expression is not a valid variant of the data type " + self.type + "."
    end
  | errCasesPatternNumberFields(name, expected, given) with: tostring(self):
      "The variant pattern for cases branch " + self.name + " should have " + tostring(self.expected) + " fields, not " + tostring(self.given)  + "."
    end
  | errCasesBranchType(type1, type2, name) with: tostring(self):
      "All branches of a cases expression must evaluate to the same type. Found branches with type " + self.type1 +", which is incompatible with the type of branch " + self.name + ", which has type " + self.type2 + "."
    end
  | errTypeNotDefined(type) with: tostring(self):
      "The " + self.type + " type is not defined. Did you forget to import, or forget to add the type parameter?"
    end
  | errIfTestNotBool(ty) with: tostring(self):
      "The test of the if expression has type " + self.ty + ", which is not a Bool."
    end
  | errIfBranchType(type1, type2) with: tostring(self):
      "All branches of an if expression must evaluate to the same type. Found branches with type " + self.type1 + " which is incompatible with this branch, which has type " + self.type2 + "."
    end
  | errAnnDotNotSupported(obj, field) with: tostring(self):
      "Dotted annotations are currently not supported, so we are treating " + self.obj + "." + self.field + " as the Dynamic type."
    end
end

fun msg(err :: TCError) -> String:
  tostring(err)
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
    | anyType => "Any*"
    | nameType(name) => name
    | anonType(rec) =>
      cases(RecordType) rec:
        | normalRecord(fields) =>
          "{" + fmfields(fields) + "}"
        | moreRecord(fields) =>
          "{" + fmfields(fields) + "...}"
      end
    | arrowType(args, ret, rec) => fmarrow([], args, ret)
    | methodType(self, args, ret, rec) => fmarrow([], [self]+args, ret)
    | appType(name, args) => name + "<" + args.map(fmty).join-str(", ") + ">"
    | bigLamType(params, ty) =>
      cases(Type) ty:
        | arrowType(args, ret, rec) => fmarrow(params, args, ret)
        | methodType(self, args, ret, rec) => fmarrow(params, self^link(args), ret)
        | appType(name, args) =>
          name + "[" + params.join-str(", ") + "]" + "<" + args.map(fmty).join-str(", ") + ">"
        | else =>
          "[" + params.join-str(", ") + "]" + fmty(type)
      end
  end
where:
  fmty(appType("Option", [nmty("Element")])) is "Option<Element>"
  fmty(bigLamType(["T"], appType("List", [nmty("T")]))) is "List[T]<T>"
  fmty(appType("Either", [nmty("T"), nmty("U")])) is "Either<T, U>"
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

fun ordinalize(n :: Number) -> String:
  if (n > 10) and (n < 21):
    tostring(n) + "th"
  else:
    m = n.modulo(10)
    if m == 1:
      tostring(n) + "st"
    else if m == 2:
      tostring(n) + "nd"
    else if m == 3:
      tostring(n) + "rd"
    else:
      tostring(n) + "th"
    end
  end
where:
  ordinalize(1) is "1st"
  ordinalize(2) is "2nd"
  ordinalize(3) is "3rd"
  [4,5,6,7,8,9,10,11,12,13,14,20,100].map(fun(n): ordinalize(n) is tostring(n) + "th" end)
  [21,101,131].map(fun(n): ordinalize(n) is tostring(n) + "st" end)
  [22, 122, 10232].map(fun(n): ordinalize(n) is tostring(n) + "nd" end)
  [23, 123, 1023].map(fun(n): ordinalize(n) is tostring(n) + "rd" end)
end

fun<A> zip2(l1 :: List<A>, l2 :: List<B>) -> List<Pair<A,B>>:
  doc: "Will fail if the second list is shorter than first."
  cases(List<A>) l1:
    | empty => empty
    | link(f, r) => link(pair(f, l2.first), zip2(r, l2.rest))
  end
end


################################################################################
# Basic helper functions.                                                      #
################################################################################

fun nmty(name :: String) -> Type:
  nameType(name)
end

fun appty(name :: String, args :: List) -> Type:
  appType(name, args.map(fun(t): if String(t): nmty(t) else: t end end))
end

fun params-wrap(ps :: List<String>, t :: Type):
  if ps == []:
    t
  else:
    bigLamType(ps, t)
  end
end

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

fun tyequal(t1 :: Type, t2 :: Type) -> Bool:
  doc: "Type equality, allowing for moreRecords containing unknown additional fields."
  cases(Type) t1:
    | nameType(name1) =>
      cases(Type) t2:
        | nameType(name2) => name1 == name2
        | else => false
      end
    | anonType(rec1) =>
      cases(Type) t2:
        | anonType(rec2) =>
          recequal(rec1, rec2)
        | else => false
      end
    | arrowType(args1, ret1, rec1) =>
      cases(Type) t2:
        | arrowType(args2, ret2, rec2) =>
          (args1 == args2) and (ret1 == ret2) and recequal(rec1, rec2)
        | else => false
      end
    | methodType(self1, args1, ret1, rec1) =>
      cases(Type) t2:
        | methodType(self2, args2, ret2, rec2) =>
          (self1 == self2) and (args1 == args2) and (ret1 == ret2) and recequal(rec1, rec2)
        | else => false
      end
    | appType(name1, args1) =>
      cases(Type) t2:
        | appType(name2, args2) =>
          (name1 == name2) and (args1 == args2)
        | else => false
      end
    | dynType => t2 == dynType
    | anyType => t2 == anyType
  end
where:
  tyequal(nmty("A"), nmty("A")) is true
  tyequal(nmty("A"), nmty("B")) is false
  tyequal(anonType(normalRecord([])), anonType(moreRecord([pair("b", nmty("Number"))]))) is false
  tyequal(anonType(normalRecord([])), anonType(normalRecord([]))) is true
  tyequal(anonType(normalRecord([])), anonType(normalRecord([pair("b", nmty("Number"))]))) is false
  tyequal(nmty("A"), arrowType([], nmty("A"), moreRecord([]))) is false
  tyequal(arrowType([], nmty("A"), moreRecord([pair("b", nmty("Number"))])), arrowType([], nmty("A"), moreRecord([]))) is true
  tyequal(arrowType([], nmty("A"), normalRecord([pair("b", nmty("Number"))])), arrowType([], nmty("A"), moreRecord([]))) is true
  tyequal(arrowType([], nmty("A"), normalRecord([pair("b", nmty("Number"))])), arrowType([], nmty("A"), normalRecord([]))) is false
  tyequal(arrowType([], nmty("A"), normalRecord([])), arrowType([], nmty("A"), moreRecord([pair("b", nmty("Number"))]))) is false
end

fun tycompat(t1 :: Type, t2 :: Type) -> Bool:
  doc: "equality with Dyn"
  cases(Type) t1:
    | dynType => true
    | else =>
      cases(Type) t2:
        | dynType => true
        | else => t1 == t2
      end
  end
end

fun get-type(ann :: A.Ann) -> TCST<Type>:
  cases(A.Ann) ann:
    | a_blank => return(dynType)
    | a_any => return(anyType)
    | a_name(l, id) =>
      get-type-env()^bind(fun(type-env):
          cases(Option) map-get(type-env, nmty(id)):
            | some(tyb) =>
              cases(TypeBinding) tyb:
                | typeNominal(_) => return(nmty(id))
                | typeAlias(ty) => return(ty)
              end
            | none =>
              add-error(l, msg(errTypeNotDefined(fmty(nmty(id)))))^seq(
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
          return(anonType(normalRecord(fieldsty)))
        end)
    | a_app(l, ann1, args) =>
      cases(A.Ann) ann1:
        | a_name(l1, id) => sequence(args.map(get-type))^bind(fun(argtys):
              return(appType(id, argtys))
            end)
        | a_dot(l1,obj,field) => add-error(l1, errAnnDotNotSupported(obj, field))^seq(return(dynType))
        | else => raise("tc: got an ann at " + torepr(l) + " inside of a_app that is not an a_name or a_dot, which shouldn't be able to happen: " + torepr(ann1))
      end
    | a_dot(l, obj, field) => add-error(l, errAnnDotNotSupported(obj, field))^seq(return(dynType))
    | a_pred(l, ann1, _) => get-type(ann1)
  end
end

fun type-record-add(orig :: Type, field :: String, type :: Type) -> Type:
  cases(Type) orig:
      # NOTE(dbp 2013-11-05): What do we do in this case? ...rrg.
    | nameType(name) => nameType(name)
    | anonType(record) =>
      cases(RecordType) record:
        | normalRecord(fields) =>
          anonType(normalRecord([pair(field, type)] + fields))
        | moreRecord(fields) =>
          anonType(moreRecord([pair(field, type)] + fields))
      end
      # NOTE(dbp 2013-10-16): Can we start treating this as something
      # better? moreRecord or something?
    | dynType => dynType
    | anyType => anyType
    | else => raise("type-record-add: didn't match " + torepr(orig))
  end
where:
  my-type = anonType(normalRecord([]))
  type-record-add(my-type, "foo", my-type)
  is anonType(normalRecord([pair("foo", my-type)]))
  my-more-type = anonType(moreRecord([]))
  type-record-add(my-more-type, "foo", my-type)
    is anonType(moreRecord([pair("foo", my-type)]))
end

data TySolveRes:
  | allSolved(l :: List<Type>)
  | someSolved(l :: List<Type>)
  | incompatible
end

fun tysolve(vars :: List<String>, _eqs :: List<Pair<Type, Type>>, tys :: List<Type>) -> TySolveRes:
  doc: "Solves for vars using eqs (by constraint generation/elimination) and uses those to substitute into tys.
        If all are not solved for, returning none. This is how we instantiate type parameters through local inference."

  fun congen(eqs :: List<Pair<Type, Type>>) -> List<Pair<String,Type>>:
    doc: "Output are pairs of v, ty, where v is a name in vars that should equal ty"
    fun recgen(r1 :: RecordType, r2 :: RecordType) -> List<Pair<String, Type>>:
      fun recgen-int(f1, f2):
        cases(List) f1:
          | empty => empty
          | link(p1,r) =>
            cases(Option) map-get(f2, p1.a):
              | none => raise(nothing)
              | some(p2) =>
                congen(link(pair(p1.b, p2), recgen-int(r, f2.rest)))
            end
        end
      end
      if (r1.fields.length() <> r2.fields.length()) or
        (not list.all(fun(x): x end, r1.fields.map(_.a).map(r2.fields.map(_.a).member(_)))):
        raise(nothing)
      else:
        recgen-int(r1.fields, r2.fields)
      end
    end
    cases(List) eqs:
      | empty => empty
      | link(tp, r) =>
        cases(Pair) tp:
          | pair(t1, t2) =>
            cases(Type) t1:
              | nameType(n1) =>
                if vars.member(n1):
                  link(pair(n1, t2), congen(r))
                else:
                  if is-nameType(t2) and vars.member(t2.name):
                      link(pair(t2.name, t1), congen(r))
                  else if is-dynType(t2):
                    congen(r)
                  else:
                    raise(nothing)
                  end
                end
              | anonType(rec1) =>
                (cases(Type) t2:
                  | anonType(rec2) =>
                    recgen(rec1, rec2)
                  | else => raise(nothing)
                  end) + congen(r)
              | arrowType(args1, ret1, rec1) =>
                cases(Type) t2:
                  | arrowType(args2, ret2, rec2) =>
                    if args1.length() <> args2.length():
                      raise(nothing)
                    else:
                      congen(link(pair(ret1, ret2), zip2(args1, args2))) +
                      recgen(rec1, rec2) + congen(r)
                    end
                  | else =>
                    if is-nameType(t2) and vars.member(t2.name):
                      link(pair(t2.name, t1), congen(r))
                    else:
                      raise(nothing)
                    end
                end
              | methodType(self1, args1, ret1, rec1) =>
                cases(Type) t2:
                  | methodType(self2, args2, ret2, rec2) =>
                    if args1.length() <> args2.length():
                      raise(nothing)
                    else:
                      congen(link(pair(self1, self2), link(pair(ret1, ret2), zip2(args1, args2)))) +
                      recgen(rec1, rec2) + congen(r)
                    end
                  | else =>
                    if is-nameType(t2) and vars.member(t2.name):
                      link(pair(t2.name, t1), congen(r))
                    else:
                      raise(nothing)
                    end
                end
              | appType(name1, args1) =>
                cases(Type) t2:
                  | appType(name2, args2) =>
                    if (args1.length() <> args2.length()) or (name1 <> name2):
                      raise(nothing)
                    else:
                      congen(zip2(args1, args2)) + congen(r)
                    end
                  | else =>
                    if is-nameType(t2) and vars.member(t2.name):
                      link(pair(t2.name, t1), congen(r))
                    else:
                      raise(nothing)
                    end
                end
              | dynType =>
                if t2 == dynType:
                  congen(r)
                else if is-nameType(t2) and vars.member(t2.name):
                  link(pair(t2, t1), congen(r))
                else:
                  raise(nothing)
                end
              | anyType =>
                if t2 == anyType:
                 congen(r)
                else if is-nameType(t2) and vars.member(t2.name):
                  link(pair(t2, t1), congen(r))
                else:
                  raise(nothing)
                end
            end
        end
    end
  end

  var loop-point = nothing

  fun consolve(cons :: List<Pair<String, Type>>) -> List<Pair<String,Type>>:
    doc: "Output has unique left sides, all in vars."
    cases(List<Pair<String,Type>>) cons:
      | empty => empty
      | link(p, rest) =>
        cases(Pair<String, Type>) p:
          | pair(a, b) =>
            if nmty(a) == b:
              consolve(rest)
            else if vars.member(a):
              if appears(a, b):
                raise(nothing)
              else if list.any(fun(x): x end, vars.map(appears(_, b))):
                if (not Nothing(loop-point)) and identical(loop-point, p):
                  # don't go into infinite loops.
                  raise(nothing)
                else:
                  when Nothing(loop-point):
                    loop-point := p
                  end
                  consolve(rest + [p])
                end
              else:
                link(pair(a, b), consolve(rest.map(fun(r):
                        if r.a == a:
                          if r.b == b:
                            pair(r.a, nmty(r.a))
                          else if is-nameType(r.b) and vars.member(r.b.name):
                            pair(r.b.name, b)
                          else:
                            raise(nothing)
                          end
                        else:
                          pair(r.a, replace(a, b, r.b))
                        end
                      end)))
              end
            else:
              raise("tysolve: invariant violated - left side should be var.")
            end
        end
    end
  end

  fun appears(v :: String, t :: Type) -> Bool:
    fun rec-appears(_v :: String, r :: RecordType) -> Bool:
      list.any(fun(x): x end, r.fields.map(_.b).map(appears(_v,_)))
    end
    cases(Type) t:
      | nameType(name) => name == v
      | anonType(rec) => rec-appears(v, rec)
      | arrowType(args, ret, rec) =>
        list.any(fun(x): x end, args.map(appears(v,_))) or appears(v, ret) or rec-appears(v, rec)
      | methodType(self, args, ret, rec) =>
        list.any(fun(x): x end, args.map(appears(v,_))) or  appears(v, self) or appears(v, ret) or rec-appears(v, rec)
      | appType(name, args) =>
        list.any(fun(x): x end, args.map(appears(v,_)))
      | dynType => false
      | anyType => false
    end
  end

  fun replace(v :: String, nt :: Type, t :: Type) -> Type:
    doc: "replace any occurrence of nameType(n) with nt in t"
    fun rec-replace(_v :: String, _nt :: Type, r :: RecordType) -> Bool:
      cases(RecordType) r:
        | normalRecord(fields) =>
          normalRecord(fields.map(fun(p): pair(p.a, replace(_v,_nt,p.b)) end))
        | moreRecord(fields) =>
          moreRecord(fields.map(fun(p): pair(p.a, replace(_v,_nt,p.b)) end))
      end
    end
    cases(Type) t:
      | nameType(name) => if name == v: nt else: t end
      | anonType(rec) => anonType(rec-replace(v, nt, rec))
      | arrowType(args, ret, rec) =>
        arrowType(args.map(replace(v,nt,_)), replace(v,nt,ret), rec-replace(v,nt, rec))
      | methodType(self, args, ret, rec) =>
        methodType(replace(v,nt,self), args.map(replace(v,nt,_)), replace(v,nt,ret), rec-replace(v,nt, rec))
      | appType(name, args) =>
        appType(name, args.map(replace(v,nt,_)))
      | dynType => false
      | anyType => false
    end
  end

  fun conreplace(sols :: List<Pair<String,Type>>, _tys :: List<Type>) -> TySolveRes:
    replaced = for fold(acc from _tys, sol from sols):
      acc.map(replace(sol.a, sol.b, _))
    end
    if list.any(fun(x): x end, replaced.map(fun(r): list.any(fun(x): x end, vars.map(appears(_, r))) end)):
      someSolved(for fold(acc from replaced, v from vars):
          acc.map(replace(v, dynType, _))
        end)
    else:
      allSolved(replaced)
    end
  end

  try:
    _eqs^congen()^consolve()^conreplace(tys)
  except(e):
    if e == nothing:
      incompatible
    else:
      raise(e)
    end
  end
where:
  tysolve(["T"], [pair(appty("Foo", ["T"]), appty("Foo", ["String"]))],
    [appty("Bar", ["T"])]) is allSolved([appty("Bar", ["String"])])

  tysolve(["T"], [pair(nmty("T"), appty("Foo", ["String"]))],
    [appty("Bar", ["T"])]) is allSolved([appty("Bar", [appty("Foo", ["String"])])])

  tysolve(["T"], [pair(appty("Foo", ["T"]), appty("Foo", ["String"])),
    pair(nmty("T"), nmty("String"))],
    [appty("Bar", ["T"]), nmty("U")]) is allSolved([appty("Bar", ["String"]), nmty("U")])

  tysolve(["T"], [pair(nmty("T"), nmty("Number")), pair(nmty("T"), nmty("String"))], []) is incompatible

  tysolve(["T", "U"], [pair(nmty("U"), nmty("Number")),
      pair(anonType(moreRecord([pair("f", nmty("T"))])), nmty("String"))], []) is incompatible

  tysolve(["T", "U"], [pair(nmty("U"), nmty("Number")),
      pair(anonType(moreRecord([pair("f", nmty("T"))])), anonType(moreRecord([pair("f", nmty("String"))])))],
    [nmty("U"), nmty("T")]) is allSolved([nmty("Number"), nmty("String")])

  tysolve(["T", "U"], [pair(nmty("T"), nmty("U")), pair(nmty("T"), nmty("String"))], [nmty("U")])
  is allSolved([nmty("String")])

  tysolve(["T", "U"], [pair(nmty("T"), nmty("U")), pair(nmty("U"), nmty("T"))], [nmty("U")]) is incompatible

  tysolve(["T", "U"], [pair(nmty("T"), nmty("U")), pair(nmty("U"), nmty("T"))], [nmty("U")]) is incompatible

  tysolve(["T"], [pair(arrowType([nmty("T")], appty("Foo", ["T"]), moreRecord([])),
        arrowType([nmty("Bool")], appty("Foo", ["String"]), moreRecord([])))], [appty("Foo", ["T"])]) is incompatible

  tysolve(["T"], [pair(arrowType([nmty("T")], appty("Foo", ["T"]), moreRecord([])),
        arrowType([nmty("Bool")], appty("Foo", ["Bool"]), moreRecord([])))], [nmty("T")]) is allSolved([nmty("Bool")])

  tysolve(["T"], [pair(nmty("T"), appty("Option", ["T"]))], []) is incompatible

  tysolve(["T"], [pair(nmty("String"), appty("Option", ["T"]))], []) is incompatible

  tysolve(["T"], [pair(nmty("String"), appty("Option", ["Number"]))], []) is incompatible

  tysolve(["T"], [pair(nmty("U"), appty("Option", ["Number"]))], [nmty("T")]) is incompatible

  tysolve(["T", "U"], [pair(nmty("T"), appty("Foo", [appty("Bar", ["U"])])),
                            pair(nmty("String"), nmty("U"))],
    [nmty("T"), nmty("U")]) is allSolved([appty("Foo", [appty("Bar", ["String"])]), nmty("String")])

  tysolve(["T"], [pair(appty("Foo", ["T"]), appty("Foo", [anyType]))], [nmty("T")]) is allSolved([anyType])

  tysolve(["T", "U"], [pair(nmty("T"), nmty("String"))], [nmty("T"), nmty("U")]) is someSolved([nmty("String"), dynType])
end


################################################################################
# Binding extraction, letrec behavior, datatype bindings.                      #
################################################################################

fun bind-params(params, mv) -> TCST:
  add-types(params.map(fun(n):
      pair(nmty(n), typeNominal(anonType(normalRecord([]))))
      end), mv)
end

fun get-bindings(ast :: A.Expr) -> TCST<List<Pair<String, Type>>>:
  doc: "This function implements letrec behavior."
  fun name-val-binds(name, val):
    if A.is-a_blank(name.ann):
      cases(A.Expr) val:
        | s_lam(l1, ps, args, ann, doc, body, ck) =>
          bind-params(ps,
            sequence(args.map(fun(b): get-type(b.ann) end))^bind(fun(arg-tys):
                get-type(ann)^bind(fun(ret-ty):
                    return([pair(name.id, params-wrap(ps, arrowType(arg-tys, ret-ty, moreRecord([]))))])
                  end)
              end)
            )
        | else =>
          # NOTE(dbp 2013-11-07): This seems buggy - we want to type check
          # it if it is something simple (like a number, string, application),
          # but not if it can have things like functions in it.
          tc(val)^bind(fun(ty): return([pair(name.id, ty)]) end)
      end
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
      bind-params(params,
        sequence(variants.map(get-variant-bindings(name, params, _)))^bind(fun(vbs):
            return(vbs^concat() + [pair(name, params-wrap(params, arrowType([anyType], nmty("Bool"), moreRecord([]))))])
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
  boolty = nmty("Bool")
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
    | s_datatype_variant(l, vname, members, constr) =>
      sequence(members.map(get-member-type))^bind(fun(memtys):
          return([pair(vname, params-wrap(tparams, arrowType(memtys, bigty, moreRecord([])))),
              pair("is-" + vname, arrowType([anyType], boolty, moreRecord([])))])
        end)
    | s_datatype_singleton_variant(l, vname, constr) =>
      return([pair(vname, bigty),
          pair("is-" + vname, arrowType([anyType], boolty, moreRecord([])))])
  end
where:
  # NOTE(dbp 2013-10-30): I don't like writing tests with the ast written out
  # like this, as it seems fragile, but I don't think we have a way of parsing
  # fragments, and parsing larger programs and extracting the parts out doesn't
  # seem any less fragile
  dummy-loc = loc("dummy-file", -1, -1)
  footy = nmty("Foo")
  boolty = nmty("Bool")
  strty = nmty("String")
  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [], default-type-env)
  is
  [pair("foo", arrowType([], footy, moreRecord([]))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))]

  eval(get-variant-bindings("Foo", ["T"],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", bigLamType(["T"],arrowType([strty], footy, moreRecord([])))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))]


  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [],[],default-type-env)
  is
  [pair("foo", arrowType([strty, boolty], footy, moreRecord([]))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))]
end

fun get-type-bindings(ast :: A.Expr) -> TCST<List<Pair<String>>>:
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      sequence(stmts.map(get-type-bindings))^bind(fun(bs): return(concat(bs)) end)
    | s_user_block(l, block) => get-type-bindings(block)
    | s_datatype(l, name, params, _, _) =>
      if params == []:
        return([pair(nmty(name), typeNominal(anonType(moreRecord([]))))])
      else:
        return([pair(nmty(name), typeAlias(bigLamType(params, appType(name, params.map(nmty))))),
            pair(params-wrap(params, appty(name, params)), typeNominal(anonType(moreRecord([]))))])
      end
    | else => return([])
  end
where:
  fun gtb-src(src):
    eval(get-type-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [])
  end
  gtb-src("x = 2") is []
  gtb-src("datatype Foo: | foo with constructor(self): self end end") is [pair(nmty("Foo"), typeNominal(anonType(moreRecord([]))))]
  gtb-src("datatype Foo: | foo with constructor(self): self end end
           datatype Bar: | bar with constructor(self): self end end") is
  [pair(nmty("Foo"), typeNominal(anonType(moreRecord([])))), pair(nmty("Bar"), typeNominal(anonType(moreRecord([]))))]

  gtb-src("datatype Foo<T>: | foo with constructor(self): self end end") is
  [pair(nmty("Foo"), typeAlias(bigLamType(["T"], appType("Foo", [nmty("T")])))),
    pair(bigLamType(["T"], appty("Foo", ["T"])), typeNominal(anonType(moreRecord([]))))]
end


################################################################################
# is-inference: inferring types from the way they are used in check-blocks.    #
################################################################################

fun is-inferred-functions(ast :: A.Expr) -> TCST<List<Pair<String, Type>>>:
  fun find-is-pairs(name :: String, e :: A.Expr) -> TCST<List<Type>>:
    cases(A.Expr) e:
      | s_block(l, stmts) => sequence(stmts.map(find-is-pairs(name, _)))^bind(fun(ps): return(concat(ps)) end)
      | s_check_test(_, op, l, r) =>
        if op == "opis":
          # NOTE(dbp 2013-10-21): Really simple for now - only if it
          # is of form funname(args) is bar.
          cases(A.Expr) l:
            | s_app(l1, fn, args) =>
              cases(A.Expr) fn:
                | s_id(l2, fname) =>
                  if fname == name:
                    tc(r)^bind(fun(rightty):
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
  iif-src("fun f(x): add1(x) where: f('Fo') is 10 end") is
  [pair("f", arrowType([nmty("String")], nmty("Number"), baseRec))]
end


################################################################################
# Subtyping.                                                                   #
################################################################################

# FIXME(dbp 2013-11-05): The naive implementation of this, which resolves names
# to records through the type env, is broken with aliases because it infinite loops very easily.
# what I have now is a very naive avoidance - ie, I only expand one level, but
# obviously this should be replaced with something more correct (with cycle detection).
# for now, this doesn't matter, since we don't have type aliases in the language.
fun subtype(l :: Loc, _child :: Type, _parent :: Type) -> TCST<Bool>:
  fun subtype-int(recur :: Bool, child :: Type, parent :: Type) -> TCST<Bool>:
    fun record-subtype(childR :: RecordType, parentR :: RecordType) -> TCST<Bool>:
      fun match-child(parent-fields, child-fields):
        for foldm(rv from true, fld from parent-fields):
          cases(Option) map-get(child-fields, fld.a):
            | none => return(false)
            | some(cty) => subtype-int(recur, cty, fld.b)^bind(fun(st): return(rv and st) end)
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
      | dynType => return(true)
      | anyType => return(true)
      | arrowType(parentargs, parentret, parentrecord) =>
        cases(Type) child:
          | dynType => return(true)
          | arrowType(childargs, childret, childrecord) =>
            subtype-int(recur, parentret, childret)^bind(fun(retres):
                for foldm(wt from (childargs.length() == parentargs.length()) and
                    retres,
                    cp from (map2(pair, childargs, parentargs))):
                  subtype-int(recur, cp.a, cp.b)^bind(fun(wt2): return(wt and wt2) end)
                end
              end)
          | else => return(false)
        end
      | methodType(parentself, parentargs, parentret, parentrecord) =>
        cases(Type) child:
          | dynType => return(true)
          | methodType(childself, childargs, childret, childrecord) =>
            subtype-int(recur, parentret, childret)^bind(fun(retres):
                subtype-int(recur, childself, parentself)^bind(fun(selfres):
                    for foldm(wt from (childargs.length() == parentargs.length()) and
                        retres and selfres,
                        cp from (map2(pair, childargs, parentargs))):
                      subtype-int(recur, cp.a, cp.b)^bind(fun(wt2): return(wt and wt2) end)
                    end
                  end)
              end)
          | else => return(false)
        end
      | nameType(parentname) =>
        cases(Type) child:
          | dynType => return(true)
          | anyType =>
            if not recur:
              return(false)
            else:
              get-type-env()^bind(fun(type-env):
                  cases(Option) map-get(type-env, parent):
                    | none =>
                      add-error(l, msg(errTypeNotDefined(fmty(parent))))^seq(
                        return(false))
                    | some(parentbind) =>
                      cases(TypeBinding) parentbind:
                        | typeNominal(_) => return(false)
                        | typeAlias(parentty) =>
                          return(parentty == anyType)
                      end
                  end
                end)
            end
          | nameType(childname) =>
            if parentname == childname:
              return(true)
            else:
              if not recur:
                return(false)
              else:
                get-type-env()^bind(fun(type-env):
                    cases(Option) map-get(type-env, parent):
                      | none =>
                        add-error(l, msg(errTypeNotDefined(fmty(parent))))^seq(
                          return(false))
                      | some(parentbind) =>
                        cases(TypeBinding) parentbind:
                          | typeNominal(_) =>
                            cases(Option) map-get(type-env, child):
                              | none =>
                                add-error(l, msg(errTypeNotDefined(fmty(child))))^seq(
                                  return(false))
                              | some(childbind) =>
                                cases(TypeBinding) childbind:
                                  | typeNominal(_) => return(false)
                                  | typeAlias(childty) =>
                                    subtype-int(false,  childty, parent)
                                end
                            end
                          | typeAlias(parentty) =>
                            cases(Option) map-get(type-env, child):
                              | none =>
                                add-error(l, msg(errTypeNotDefined(fmty(child))))^seq(
                                  return(false))
                              | some(childbind) =>
                                cases(TypeBinding) childbind:
                                  | typeNominal(_) => subtype-int(false, child, parentty)
                                  | typeAlias(childty) =>
                                    subtype-int(false,  childty, parentty)
                                end
                            end
                        end
                    end
                  end)
              end
            end
          | else =>
            if not recur:
              return(false)
            else:
              get-type-env()^bind(fun(type-env):
                  cases(Option) map-get(type-env, parent):
                    | none =>
                      add-error(l, msg(errTypeNotDefined(fmty(parent))))^seq(
                        return(false))
                    | some(parentbind) =>
                      cases(TypeBinding) parentbind:
                        | typeNominal(_) => return(false)
                        | typeAlias(parentty) =>
                          subtype-int(false, child, parentty)
                      end
                  end
                end)
            end
        end
      | anonType(parentrecord) =>
        cases(Type) child:
          | dynType => return(true)
          | anonType(childrecord) =>
            record-subtype(childrecord, parentrecord)
          | nameType(childname) =>
            if not recur:
              return(false)
            else:
              get-type-env()^bind(fun(type-env):
                  cases(Option) map-get(type-env, child):
                    | none =>
                      add-error(l, msg(errTypeNotDefined(fmty(child))))^seq(
                        return(false))
                    | some(childbind) =>
                      cases(TypeBinding) childbind:
                        | typeNominal(_) => return(false)
                        | typeAlias(childty) =>
                          subtype-int(false, childty, parent)
                      end
                  end
                end)
            end
          | else => return(false)
        end
      | appType(parentname, parentargs) =>
        cases(Type) child:
          | dynType => return(true)
          | anyType => return(true)
          | appType(childname, childargs) =>
            if (parentname <> childname) or (parentargs.length() <> childargs.length()):
              return(false)
            else:
              # NOTE(dbp 2013-11-07): I don't know how to do this properly,
              # so I'm going to do something approximate - if no parameters,
              # do subtyping across children, if there are, do pure equality.
              sequence(map2(subtype(l,_,_), childargs, parentargs))^bind(fun(sts):
                  return(list.all(fun(x): x end, sts))
                end)
            end
          | nameType(childname) =>
            if not recur:
              return(false)
            else:
              get-type-env()^bind(fun(type-env):
                  cases(Option) map-get(type-env, child):
                    | none =>
                      add-error(l, msg(errTypeNotDefined(fmty(child))))^seq(
                        return(dynType))
                    | some(childbind) =>
                      cases(TypeBinding) childbind:
                        | typeNominal(_) => return(false)
                        | typeAlias(childty) =>
                          subtype-int(false, childty, parent)
                      end
                  end
                end)
            end
          | else => return(false)
        end
      | bigLamType(parentparams, parenttype) =>
        cases(Type) child:
          | bigLamType(childparams, childtype) =>
            # FIXME(dbp 2013-11-09): deal with differently named params.
            subtype(l, childtype, parenttype)^bind(fun(st): return(st and (parentparams == childparams)) end)
          | else =>
            if parentparams == []:
              subtype(child, parenttype)
            else:
              return(false)
            end
        end
    end
  end
  subtype-int(true, _child, _parent)
where:
  l = loc("", 0, 0)
  eval(subtype(l, anyType, anyType), [], [], [], default-type-env) is true
  numType = nmty("Number")
  eval(subtype(l, numType, anyType), [], [], [], default-type-env) is true
  eval(subtype(l, anyType, numType), [], [], [], default-type-env) is false

  eval(subtype(l, nmty("Any"), nmty("Any")), [], [], [], default-type-env) is true
  eval(subtype(l, numType, nmty("Any")), [], [], [], default-type-env) is true
  eval(subtype(l, nmty("Any"), numType), [], [], [], default-type-env) is false

  fun recType(flds): anonType(normalRecord(flds)) end

  eval(subtype(l, recType([pair("foo", anyType)]), anyType), [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", anyType)])), [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", numType)])), [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType)]), recType([pair("foo", anyType)])), [], [], [], default-type-env) is true
  eval(subtype(l, recType([]), recType([pair("foo", numType)])), [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType), pair("bar", anyType)]),
      recType([pair("foo", anyType)])), [], [], [], default-type-env) is true

  eval(subtype(l, arrowType([], dynType, moreRecord([])),
      arrowType([dynType], dynType, moreRecord([]))), [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([numType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([numType], dynType, moreRecord([]))), [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], anyType, moreRecord([])),
      arrowType([anyType], numType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], numType, moreRecord([])),
      arrowType([anyType], anyType, moreRecord([]))), [], [], [], default-type-env) is false

  eval(subtype(l, methodType(dynType, [], dynType, moreRecord([])),
      methodType(dynType, [dynType], dynType, moreRecord([]))), [], [], [], default-type-env) is false
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(numType, [numType], dynType, moreRecord([]))), [], [], [], default-type-env) is false
  eval(subtype(l, methodType(anyType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], anyType, moreRecord([])),
      methodType(anyType, [anyType], numType, moreRecord([]))), [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], numType, moreRecord([])),
      methodType(anyType, [anyType], anyType, moreRecord([]))), [], [], [], default-type-env) is false

  eval(subtype(l, anyType, nmty("Any")), [], [], [], default-type-env) is true

  eval(subtype(l, appty("Foo", []), nmty("Any")), [], [], [], default-type-env)
  is true
  eval(subtype(l, appty("Foo", []), bigLamType(["T"], appType("Foo", []))), [], [], [], default-type-env)
  is false
  eval(subtype(l, appty("Foo", ["String"]), appty("Foo", ["Any"])), [], [], [], default-type-env)
  is true
  eval(subtype(l, bigLamType(["T"], appty("Option", ["T"])), bigLamType(["T"], appty("Option", ["T"]))), [], [], [], default-type-env)
  is true

end


################################################################################
# tc Helper functions and builtin env and type-env                             #
################################################################################
fun simple-mty(self, args, ret):
  fun mkty(t):
    if String(t):
      nmty(t)
    else:
      t
    end
  end
  methodType(mkty(self), args.map(mkty), mkty(ret), moreRecord([]))
end
fun app-mty(self, param, args, ret):
  fun mkty(t):
    if String(t):
      nmty(t)
    else:
      t
    end
  end
  methodType(appty(self, [param]), args.map(mkty), mkty(ret), moreRecord([]))
end
fun param-app-mty(params, self, param, args, ret):
  fun mkty(t):
    if String(t):
      nmty(t)
    else:
      t
    end
  end
  params-wrap(params, methodType(appty(self, [param]), args.map(mkty), mkty(ret), moreRecord([])))
end
default-type-env = [
  pair(nameType("Any"), typeAlias(anyType)),
  pair(nameType("Bool"),  typeNominal(anonType(normalRecord([
            pair("_and", simple-mty("Bool", [arrowType([], nmty("Bool"), moreRecord([]))], "Bool")),
            pair("_or", simple-mty("Bool", [arrowType([], nmty("Bool"), moreRecord([]))], "Bool")),
            pair("tostring", simple-mty("Bool", [], "String")),
            pair("_torepr",  simple-mty("Bool", [], "String")),
            pair("_equals",  simple-mty("Bool", ["Any"], "Bool")),
            pair("_not", simple-mty("Bool", [], "Bool"))
          ])))),
  pair(nameType("Number"),
    typeNominal(anonType(normalRecord([
            pair("_plus", simple-mty("Number", ["Number"], "Number")),
            pair("_add", simple-mty("Number", ["Number"], "Number")),
            pair("_minus", simple-mty("Number", ["Number"], "Number")),
            pair("_divide", simple-mty("Number", ["Number"], "Number")),
            pair("_times", simple-mty("Number", ["Number"], "Number")),
            pair("_torepr", simple-mty("Number", [], "String")),
            pair("_equals", simple-mty("Number", ["Any"], "Bool")),
            pair("_lessthan", simple-mty("Number", ["Number"], "Bool")),
            pair("_greaterthan", simple-mty("Number", ["Number"], "Bool")),
            pair("_lessequal", simple-mty("Number", ["Number"], "Bool")),
            pair("_greaterequal", simple-mty("Number", ["Number"], "Bool")),
            pair("tostring", simple-mty("Number", [], "String")),
            pair("modulo", simple-mty("Number", ["Number"], "Number")),
            pair("truncate", simple-mty("Number", [], "Number")),
            pair("abs", simple-mty("Number", [], "Number")),
            pair("max", simple-mty("Number", ["Number"], "Number")),
            pair("min", simple-mty("Number", ["Number"], "Number")),
            pair("sin", simple-mty("Number", [], "Number")),
            pair("cos", simple-mty("Number", [], "Number")),
            pair("tan", simple-mty("Number", [], "Number")),
            pair("asin", simple-mty("Number", [], "Number")),
            pair("acos", simple-mty("Number", [], "Number")),
            pair("atan", simple-mty("Number", [], "Number")),
            pair("sqr", simple-mty("Number", [], "Number")),
            pair("sqrt", simple-mty("Number", [], "Number")),
            pair("ceiling", simple-mty("Number", [], "Number")),
            pair("floor", simple-mty("Number", [], "Number")),
            pair("log", simple-mty("Number", [], "Number")),
            pair("exp", simple-mty("Number", [], "Number")),
            pair("exact", simple-mty("Number", [], "Number")),
            pair("is-integer", simple-mty("Number", [], "Bool")),
            pair("expt", simple-mty("Number", ["Number"], "Number"))
          ])))
    ),
  pair(nameType("String"), typeNominal(anonType(normalRecord([
            pair("_plus", simple-mty("String", ["String"], "String")),
            pair("_lessequal", simple-mty("String", ["String"], "Bool")),
            pair("_lessthan", simple-mty("String", ["String"], "Bool")),
            pair("_greaterthan", simple-mty("String", ["String"], "Bool")),
            pair("_greaterequal", simple-mty("String", ["String"], "Bool")),
            pair("_equals", simple-mty("String", ["Any"], "Bool")),
            pair("append", simple-mty("String", ["String"], "String")),
            pair("contains", simple-mty("String", ["String"], "Bool")),
            pair("substring", simple-mty("String", ["Number", "Number"], "String")),
            pair("char-at", simple-mty("String", ["Number"], "String")),
            pair("repeat", simple-mty("String", ["Number"], "String")),
            pair("length", simple-mty("String", [], "Number")),
            pair("to-lower", simple-mty("String", [], "String")),
            pair("to-upper", simple-mty("String", [], "String")),
            pair("tonumber", simple-mty("String", [], "Number")),
            pair("tostring", simple-mty("String", [], "String")),
            pair("_torepr", simple-mty("String", [], "String"))
          ])))),
  pair(nameType("List"), typeAlias(bigLamType(["T"],appType("List", [nmty("T")])))),
  pair(bigLamType(["T"],appType("List", [nmty("T")])),
    typeNominal(anonType(normalRecord([
            pair("length", app-mty("List", "T", [], "Number")),
            pair("each", app-mty("List", "T", [arrowType([nmty("T")], nmty("Nothing"), moreRecord([]))], "Nothing")),
            pair("map", param-app-mty(["U"], "List", "T", [arrowType([nmty("T")], nmty("U"), moreRecord([]))], appty("List", ["U"]))),
            pair("filter", app-mty("List", "T", [arrowType([nmty("T")], nmty("Bool"), moreRecord([]))], appty("List", ["T"]))),
            pair("find", app-mty("List", "T", [arrowType([nmty("T")], nmty("Bool"), moreRecord([]))], appty("Option", ["T"]))),
            pair("partition", app-mty("List", "T", [arrowType([nmty("T")], nmty("Bool"), moreRecord([]))],
                anonType(normalRecord([pair("is-true", appty("List", ["T"])), pair("is-false", appty("List", ["T"]))])))),
            pair("foldr", param-app-mty(["U"], "List", "T", [arrowType([nmty("T"), nmty("U")], nmty("U"), moreRecord([])), nmty("U")], nmty("U"))),
            pair("foldl", param-app-mty(["U"], "List", "T", [arrowType([nmty("T"), nmty("U")], nmty("U"), moreRecord([])), nmty("U")], nmty("U"))),
            pair("member", app-mty("List", "T", ["T"], "Bool")),
            pair("append", app-mty("List", "T", [appty("List", ["T"])], appty("List", ["T"]))),
            pair("last", app-mty("List", "T", [], nmty("T"))),
            pair("take", app-mty("List", "T", ["Number"], appty("List", ["T"]))),
            pair("drop", app-mty("List", "T", ["Number"], appty("List", ["T"]))),
            pair("reverse", app-mty("List", "T", [], appty("List", ["T"]))),
            pair("get", app-mty("List", "T", ["Number"], nmty("T"))),
            pair("set", app-mty("List", "T", ["Number", nmty("T")], appty("List", ["T"]))),
            pair("_equals", app-mty("List", "T", ["Any"], "Bool")),
            pair("tostring", app-mty("List", "T", [], "String")),
            pair("_torepr", app-mty("List", "T", [], "String")),
            pair("sort-by", app-mty("List", "T",
                [arrowType([nmty("T"), nmty("T")], nmty("Bool"), moreRecord([])),
                  arrowType([nmty("T"), nmty("T")], nmty("Bool"), moreRecord([]))], appty("List", ["T"]))),
            pair("sort", app-mty("List", "T", [], appty("List", ["T"]))),
            pair("join-str", app-mty("List", "T", ["String"], appty("List", ["T"])))
          ])))),
  pair(nameType("Option"), typeAlias(bigLamType(["T"], appType("Option", [nmty("T")])))),
  pair(bigLamType(["T"], appType("Option", [nmty("T")])), typeNominal(anonType(moreRecord([])))),
  pair(nameType("Nothing"), typeNominal(anonType(normalRecord([]))))
]

fun tc-main(p, s):
  env = [
    pair("list", anonType(
        moreRecord([
            pair("map", bigLamType(["U", "T"], arrowType([arrowType([nmty("T")], nmty("U"), moreRecord([])), appty("List", ["T"])], appty("List", ["U"]), moreRecord([])))),
            pair("link", bigLamType(["T"], arrowType([nmty("T"), appty("List", ["T"])], appty("List", ["T"]), moreRecord([])))),
            pair("empty", bigLamType(["T"], appType("List", [nmty("T")])))
          ]))),
    pair("builtins", anonType(moreRecord([]))),
    pair("error", anonType(moreRecord([]))),
    pair("link", bigLamType(["T"], arrowType([nmty("T"), appty("List", ["T"])], appty("List", ["T"]), moreRecord([])))),
    pair("empty", bigLamType(["T"], appType("List", [nmty("T")]))),
    pair("nothing", nmty("Nothing")),
    pair("some", bigLamType(["T"], arrowType([nmty("T")], appty("Option", ["T"]), moreRecord([])))),
    pair("none", bigLamType(["T"], appType("Option", [nmty("T")]))),
    pair("true", nmty("Bool")),
    pair("false", nmty("Bool")),
    pair("print", arrowType([anyType], nmty("Nothing"), moreRecord([]))),
    pair("tostring", arrowType([anyType], nmty("String"), moreRecord([]))),
    pair("torepr", arrowType([anyType], nmty("String"), moreRecord([]))),
    pair("fold", dynType),
    pair("map", bigLamType(["U", "T"], arrowType([arrowType([nmty("T")], nmty("U"), moreRecord([])), appty("List", ["T"])], appty("List", ["U"]), moreRecord([])))),
    pair("map2", dynType),
    pair("raise", arrowType([anyType], anyType, moreRecord([]))),
    pair("identical", arrowType([anyType, anyType], nmty("Bool"), moreRecord([]))),
    pair("Racket", dynType),
    pair("List", arrowType([anyType], nmty("Bool"), moreRecord([]))),
    pair("String", arrowType([anyType], nmty("Bool"), moreRecord([]))),
    pair("Function", arrowType([anyType], nmty("Bool"), moreRecord([]))),
    pair("Bool", arrowType([anyType], nmty("Bool"), moreRecord([]))),
    pair("Number", arrowType([anyType], nmty("Bool"), moreRecord([]))),
    pair("Nothing", arrowType([anyType], nmty("Bool"), moreRecord([])))
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

fun tc-app(l :: Loc, fn :: A.Expr, args :: List<A.Expr>) -> TCST<Type>:
  tc(fn)^bind(fun(fn-ty):
      cases(Type) fn-ty:
        | arrowType(arg-types, ret-type, rec-type) =>
          if args.length() <> arg-types.length():
            add-error(l,
              msg(errArityMismatch(arg-types.length(), args.length())))^seq(
              return(dynType))
          else:
            sequence(args.map(tc))^bind(fun(arg-vals):
                (for foldm(base from pair(1, ret-type), ap from zip2(arg-types, arg-vals)):
                    subtype(l, ap.b, ap.a)^bind(fun(res):
                        if not res:
                          add-error(l,
                            msg(errArgumentBadType(base.a, fmty(ap.a), fmty(ap.b))))^seq(return(pair(base.a + 1, dynType)))
                        else:
                          return(pair(base.a + 1, base.b))
                        end
                      end)
                  end)^bind(fun(p): return(p.b) end)
              end)
          end
          # NOTE(dbp 2013-10-16): Not really anything we can do. Odd, but...
        | dynType => return(dynType)
        | else =>
          add-error(l, msg(errApplyNonFunction(fmty(fn-ty))))^seq(return(dynType))
      end
    end)
end

fun tc-cases(l :: Loc, _type :: A.Ann, val :: A.Expr, branches :: List<A.CasesBranch>, _branches-ty :: Type) -> TCST<Type>:
  fun tc-branch(branch, branches-ty) -> TCST<Type>:
    tc(branch.body)^bind(fun(branchty):
        if branches-ty == anyType: # in first branch
          return(branchty)
        else:
          if tycompat(branchty, branches-ty):
            return(branchty)
          else:
            add-error(branch.l,
              msg(errCasesBranchType(fmty(branches-ty), fmty(branchty), branch.name))
              )^seq(return(dynType))
          end
        end
      end)
  end
  get-type(_type)^bind(
    fun(type):
      tc(val)^bind(
        fun(val-ty):
          subtype(l, type, val-ty)^bind(fun(st):
              if not st:
                add-error(l,
                  msg(errCasesValueBadType(fmty(type), fmty(val-ty)))
                  )^seq(return(dynType))
              else:
                get-env()^bind(
                  fun(env):
                    for foldm(branches-ty from _branches-ty, branch from branches):
                      # TODO(dbp 2013-10-30): Need to have a data-env, so we can
                      # pick up non-bound constructors.
                      cases(Option) map-get(env, branch.name):
                        | none => add-error(branch.l,
                            msg(errCasesBranchInvalidVariant(fmty(type), branch.name))
                            )^seq(return(dynType))
                        | some(ty) =>
                          cases(Type) ty:
                            | arrowType(args, ret, rec) =>
                              # NOTE(dbp 2013-10-30): No subtyping - cases type
                              # must match constructors exactly (modulo records)
                              if not tyequal(ret, type):
                                add-error(branch.l,
                                  msg(errCasesBranchInvalidVariant(fmty(type), branch.name))
                                  )^seq(return(dynType))
                              else if args.length() <> branch.args.length():
                                add-error(branch.l,
                                  msg(errCasesPatternNumberFields(branch.name, args.length(), branch.args.length()))
                                  )^seq(return(dynType))
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
                                  tc-branch(branch, branches-ty))
                              end
                            | nameType(_) =>
                              if not tyequal(ty, type):
                                add-error(branch.l,
                                  msg(errCasesBranchInvalidVariant(fmty(type), branch.name))
                                  )^seq(return(dynType))
                              else:
                                tc-branch(branch, branches-ty)
                              end
                            | else =>
                              add-error(branch.l,
                                msg(errCasesBranchInvalidVariant(fmty(type), branch.name))
                                )^seq(return(dynType))
                          end
                      end
                    end
                  end)
              end
            end)
        end)
    end)
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
                                  subtype(l, ty, bindty)^bind(fun(st):
                                      if not st:
                                        add-error(l, msg(errAssignWrongType(name.id, fmty(bindty), fmty(ty))))^seq(
                                          return(dynType))
                                      else:
                                        return(ty)
                                      end
                                    end)
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
                                  bind-params(ps,
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
                                                  subtype(l, body-ty, ret-ty)^bind(fun(st):
                                                      if st:
                                                        return(params-wrap(ps, arrowType(arg-tys, ret-ty, moreRecord([]))))
                                                      else:
                                                        add-error(l,
                                                          if inferred:
                                                            msg(errFunctionInferredIncompatibleReturn(fmty(body-ty), fmty(ret-ty)))
                                                          else:
                                                            msg(errFunctionAnnIncompatibleReturn(fmty(body-ty), fmty(ret-ty)))
                                                          end)^seq(return(dynType))
                                                      end
                                                    end)
                                                end)
                                            end)
                                          )
                                      end)
                                    )
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
                | s_if_else(l, branches, elsebranch) =>
                  tc(elsebranch)^bind(fun(_branches-ty):
                      sequence(branches.map(fun(branch):
                            tc(branch.test)^bind(fun(ty):
                                if tycompat(nmty("Bool"), ty):
                                  return(nothing)
                                else:
                                  add-error(branch.l, msg(errIfTestNotBool(fmty(ty))))
                                end
                              end)
                          end))^seq(
                        (for foldm(branches-ty from _branches-ty, branch from branches):
                            tc(branch.body)^bind(fun(branchty):
                                if branches-ty == anyType: # was no else branch
                                  return(branchty)
                                else:
                                  if tycompat(branchty, branches-ty):
                                    return(branchty)
                                  else:
                                    add-error(branch.l,
                                      msg(errIfBranchType(fmty(branches-ty), fmty(branchty)))
                                      )^seq(return(branches-ty))
                                  end
                                end
                              end)
                          end))
                    end)
                | s_lam(l, ps, args, ann, doc, body, ck) =>
                  # NOTE(dbp 2013-11-03): Check for type shadowing.
                  bind-params(ps,
                    get-type(ann)^bind(fun(ret-ty):
                        sequence(args.map(fun(b): get-type(b.ann)^bind(fun(t): return(pair(b.id, t)) end) end))^bind(fun(new-binds):
                            add-bindings(new-binds,
                              tc(body)^bind(fun(body-ty):
                                  subtype(l, body-ty, ret-ty)^bind(fun(st):
                                      if st:
                                        return(params-wrap(ps, arrowType(new-binds.map(fun(bnd): bnd.b end), ret-ty, moreRecord([]))))
                                      else:
                                        add-error(l,
                                          msg(errFunctionAnnIncompatibleReturn(fmty(body-ty), fmty(ret-ty))))^seq(
                                          return(dynType))
                                      end
                                    end)
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
                              return(type-record-add(anonType(acc), fty.a, fty.b).record)
                          end
                        end)
                    end)^bind(fun(record):
                      return(anonType(record))
                    end)
                | s_app(l, fn, args) => tc-app(l, fn, args)
                | s_id(l, id) =>
                  get-env()^bind(fun(env):
                      cases(option.Option) map-get(env, id):
                        | none => add-error(l, msg(errUnboundIdentifier(id)))^seq(return(dynType))
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
                      | methodType(self, args, ret, rec) =>
                        arrowType(args, ret, rec)
                      | else => ty
                    end
                  end
                  cases(A.Expr) field:
                    | s_str(l1, s) =>
                      fun record-lookup(record):
                        cases(RecordType) record:
                          | normalRecord(fields) =>
                            cases(Option) map-get(fields, s):
                              | none => add-error(l, msg(errFieldNotFound(s)))^seq(return(dynType))
                              | some(ty) => return(method-apply(ty))
                            end
                          | moreRecord(fields) =>
                            cases(Option) map-get(fields, s):
                              | none => return(dynType)
                              | some(ty) => return(method-apply(ty))
                            end
                        end
                      end
                      fun record-name-lookup(name):
                        get-type-env()^bind(fun(type-env):
                            cases(Option) map-get(type-env, name):
                              | none => add-error(l, msg(errTypeNotDefined(fmty(name))))^seq(return(dynType))
                              | some(recordbind) =>
                                cases(Type) recordbind.type:
                                  | anonType(record) => record-lookup(record)
                                  | anyType => return(dynType)
                                  | dynType => return(dynType)
                                  | appType(_,_,_) => return(dynType)
                                    # NOTE(dbp 2013-11-05): Not doing cycle detection in type env. Could go into an infinite loop.
                                  | nameType(_) => record-name-lookup(recordbind.type)
                                end
                            end
                          end)
                      end
                      fun rec-loo-help(obj-ty):
                        cases(Type) obj-ty:
                          | dynType => return(dynType)
                          | anyType => return(dynType)
                          | appType(_,_) => return(dynType)
                          | anonType(record) => record-lookup(record)
                          | nameType(_) => record-name-lookup(obj-ty)
                          | bigLamType(_,t) => rec-loo-help(t)
                        end
                      end
                      tc(obj)^bind(rec-loo-help)
                    | else =>
                      # NOTE(dbp 2013-10-21): Actually type check field to see if
                      # it is a String or Dyn
                      return(dynType)
                  end
                | s_colon_bracket(l, obj, field) => return(dynType)
                | s_datatype(l, name, params, variants, check) =>
                  # NOTE(dbp 2013-10-30): Should statements have type nothing?
                  return(nmty("Nothing"))
                | s_cases(l, type, val, branches) => tc-cases(l, type, val, branches, anyType)
                | s_cases_else(l, type, val, branches, _else) =>
                  tc(_else)^bind(fun(elsety): tc-cases(l, type, val, branches, elsety) end)
                  # NOTE(dbp 2013-11-05): Since we type check
                  # pre-desugar code inside 'is' tests for inference, we need
                  # any ast nodes that could appear there (in theory, any surface syntax...)
                | s_list(l, values) => return(nmty("List"))
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
