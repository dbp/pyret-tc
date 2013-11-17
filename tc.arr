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

################################################################################
#                                                                              #
# Main Outline / Important Algorithms.                                         #
#                                                                              #
# The type checker is written with the State Monad. There are about 150 lines  #
# defining this (as Pyret doesn't have monads). If you aren't familiar with    #
# how it works, consult any of various tutorials (not on monads in general,    #
# just the state monad). The reason for this is that we have many pieces of    #
# state that we want to thread, some that we want to be able to modify locally,#
# and sometimes want to discard the accumulated state. Doing this with mutation#
# is possible, but makes it harder to test (as any test has to be aware of when#
# it is running, so it doesn't disturb existing state), and doesn't add much.  #
#                                                                              #
# Types:                                                                       #
# The type system has standard base types (Number, Bool, String, etc), a top   #
# type (Any), record types ({field :: Type,..}), and a dynamic type (Dyn). New #
# data types with variants are created with datatype, and any type can be      #
# parametrized by forall type variables (note that surface Pyret is more       #
# restrictive, so only datatype and functions definitions should have these.)  #
# There is subtyping for records (width and depth), and Any is the supertype   #
# of everything. Dyn is special - it can be super or subtype, and is sufficient#
# for replacement with any other type (this may generate warnings, but not     #
# errors). When it hits an error, the type checker keeps going, attributing    #
# the type of the erroneous expression as Dyn.                                 #
#                                                                              #
# Phases:                                                                      #
# There are three main conceptual passes to the type checker. They are:        #
#  - binding extraction.
#  - is inference
#  - type checking
#
# Binding Extraction:
# This is a block-level operation, which is a fold through the statements,
# collecting bindings and types as it goes. For functions, it takes the
# annotations specified in syntax as the type, for all other let bindings, it
# takes the annotation as the type if it exists, and if not, it type checks the
# value and uses that as the annotation, binding the identifier with type Dyn
# (so recursive definitions work). For datatypes new types are added to the
# type environment, and constructors are added to the binding environment.
#
# Is Inference:
# We infer types of functions based on 'where' blocks - anywhere we see
# foo(a,...) is z, we try to figure out types for a... and z, and then use that
# to figure out the type of foo. This is done so that later definitions can
# benefit from inference on earlier ones. The algorithm for generalizing to
# parametric types is the following:
# Given a pair of lists of types (the args and return), we look at the first
# two.  If any part of them does not match (so Number and String, but also
# List<Number> and List<String>), we take that pair, construct a new type
# variable, and replace the two wherever they appear matched through the rest
# of the list of types. We then look for more mismatches and repeat until there
# are none. Now we move to the next pair of types. This is the procedure to
# generalize two types for the function - we can use that and the next
# potential type and repeat.  As a concrete example, consider the following
# three tests:
# foo(10, 20) is 20
# foo('foo', 'bar') is 'bar'
# foo(30, true) is true
# The algorithm would proceed as follows:
# 10 and 'foo' don't match, and have types Number and String. So create new
# type variable T and replace pairwise, yielding:
# T, T -> T
# T, T -> T
# We now find no mismatches through the entire list, so this is our candidate
# type.  Now we start with the next signature, and work off of this pair:
# T, T -> T
# Number, Bool -> Bool
# The first don't match, so we create a new type variable U and replace
# pairwise, to get:
# U, T -> T
# U, Bool -> Bool
# Now the first argument matches, so work on the second. It doesn't match, so
# create a new type variable V and replace pairwise:
# U, V -> V
# U, V -> V
# And now we've (successfully) inferred a proper type for this function.
#
# Type Checking: This is mostly straightforward typechecking, with the usual
# co/contravariance for subtyping with functions, making sure all branches of
# if/cases have the same type, etc.  The only thing that is a bit tricky is
# inferring instantiations for type variables.  This comes up in two ways: in
# the application of polymorphic functions, we need to figure out any type
# variables in the return type, so for example: fun<A> head(List<A>) -> A, when
# applied to a List<Number>, we need to figure out that A is Number in this
# application. The other place is in datatype. The straightforward cases is the
# same as with functions - figuring out the type of a constructed type, like
# link(10, list-of-numbers) :: List<Number>. The harder case is when the
# variant does not actually mention the type variable, for example, empty. We
# do this by normal type inference, in the local contexts where it is needed
# (so the context of empty should allow us to instantiate the A type
# variable). This also occurs with cases, which is almost always written
# as cases(List), but List is a type function, not a type, so we need to infer
# what the type of the parameter A should be.
#
################################################################################


provide {
  main: tc-main,
  format-type: fmty
} end

import pyret-eval as E
import ast as A
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

data TypeWarning:
  | typeWarning(location :: Loc, message :: String)
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

data TypeInferred:
  | typeInferred
  | typeNotInferred
end

data TypeBinding:
  | typeAlias(type :: Type)
  | typeNominal(type :: Type)
end

# used in testing
dummy-loc = loc("dummy-file", -1, -1)

#####################################################################
#                                                                   #
#     This is a big State Monad, so we can thread all the stuff.    #
#                                                                   #
#####################################################################

data TCstate:
  | tcst(
      value,
      errors :: List<TypeError>,
      warnings :: List<TypeWarning>,
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
  fun(er,w,i,e,t): tcst(v,er,w,i,e,t) end
end
fun bind(mv, mf):
  fun(er,w,i,e,t):
    p = mv(er,w,i,e,t)
    mf(p.value)(p.errors,p.warnings,p.iifs,p.env,p.type-env)
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
  fun(er,w,i,e,t):
    tcst(er,er,w,i,e,t)
  end
end
fun get-warnings():
  fun(er,w,i,e,t):
    tcst(w,er,w,i,e,t)
  end
end
fun get-iifs():
  fun(er,w,i,e,t):
    tcst(i,er,w,i,e,t)
  end
end
fun get-env():
  fun(er,w,i,e,t):
    tcst(e,er,w,i,e,t)
  end
end
fun get-type-env():
  fun(er,w,i,e,t):
    tcst(t,er,w,i,e,t)
  end
end
fun put-errors(errors):
  fun(er,w,i,e,t):
    tcst(nothing,errors,w,i,e,t)
  end
end
fun put-warnings(warnings):
  fun(er,w,i,e,t):
    tcst(nothing,er,warnings,i,e,t)
  end
end
fun put-iifs(iifs):
  fun(er,w,i,e,t):
    tcst(nothing,er,w,iifs,e,t)
  end
end
fun put-env(env):
  fun(er,w,i,e,t):
    tcst(nothing,er,w,i,env,t)
  end
end
fun put-type-env(type-env):
  fun(er,w,i,e,t):
    tcst(nothing,er,w,i,e,type-env)
  end
end
fun run(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env)
end
fun eval(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).value
end
fun exec-errors(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).errors
end
fun exec-warns(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).warnings
end
fun exec-iifs(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).iifs
end
fun exec-env(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).type-env
end
fun exec-type-env(st-prog, errs, warns, iifs, env, type-env):
  st-prog(errs,warns,iifs,env,type-env).type-env
end

# And finally, application specific actions (note that errors are
# threaded, binds and types are not.)
fun add-error(l,e):
  doc: "adds an error to the threaded state"
  get-errors()^bind(fun(errors): put-errors(errors + [pair(l,e)]) end)
end
fun add-warning(l,e):
  doc: "adds a warning to the threaded state"
  get-warnings()^bind(fun(warnings): put-warnings(warnings + [pair(l,e)]) end)
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
    [], [], [], [], []
    ) is "hello"
  exec-errors(
    add-error("l1", "error 1")^seq(add-error("l2", "error 2"))
      ^seq(return("hello")),
    [], [], [], [], []
    ) is [pair("l1","error 1"), pair("l2","error 2")]
  exec-env(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], [], []
    ) is []
  eval(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], [], []
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
  | errCasesBranchInvalidVariant(type, name, branchty) with: tostring(self):
      "The branch " + self.name + " in the cases expression is not a valid variant of the data type " + self.type + " (it has type " + self.branchty + ")."
    end
  | errCasesPatternNumberFields(name, expected, given) with: tostring(self):
      "The variant pattern for cases branch " + self.name + " should have " + tostring(self.expected) + " fields, not " + tostring(self.given)  + "."
    end
  | errCasesBranchType(types) with: tostring(self):
      "All branches of a cases expression must evaluate to the same type. Found branches with incompatible types: " + self.types.join-str(", ") +"."
    end
  | errTypeNotDefined(type) with: tostring(self):
      "The " + self.type + " type is not defined. Did you forget to import, or forget to add the type parameter?"
    end
  | errIfTestNotBool(ty) with: tostring(self):
      "The test of the if expression has type " + self.ty + ", which is not a Bool."
    end
  | errIfBranchType(types) with: tostring(self):
      "All branches of an if expression must evaluate to the same type. Found branches with incompatible types: " + self.types.join-str(", ") + "."
    end
  | errAnnDotNotSupported(obj, field) with: tostring(self):
      "Dotted annotations are currently not supported, so we are treating " + self.obj + "." + self.field + " as the Dynamic type."
    end
  | errFunctionArgumentsIncompatible(fnty, arg-tys) with: tostring(self):
      "Function with type " + self.fnty + " not compatible with arguments " + self.arg-tys.join-str(", ") + "."
    end
  | errAppTypeNotWellFormed(inst, gen) with: tostring(self):
      "Type " + self.inst + " is not a well-formed instance of the type " + self.gen + "."
    end
end

data TCWarning:
  | warnFunctionBodyDyn(retty) with: tostring(self):
      "Function body had " + self.retty + " specified as a return type, but type checker found Dyn."
    end
end

fun msg(err :: TCError) -> String:
  tostring(err)
end

fun wmsg(warn :: TCWarning) -> String:
  tostring(warn)
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

fun<A,B> zip2(_l1 :: List<A>, _l2 :: List<B>) -> List<Pair<A,B>>:
  doc: "Will fail if the second list is shorter than first."
  fun zip2h(l1, l2):
    cases(List<A>) l1:
      | empty => empty
      | link(f, r) => link(pair(f, l2.first), zip2(r, l2.rest))
    end
  end
  if _l1.length() <> _l2.length():
    raise("zip2: arguments not of the same length: " + torepr(_l1) + " and " + torepr(_l2))
  else:
    zip2h(_l1, _l2)
  end
end

fun<A,B> unzip2(l :: List<Pair<A,B>>) -> Pair<List<A>, List<B>>:
  cases(List) l:
    | empty => pair([],[])
    | link(f, r) =>
      rp = unzip2(r)
      pair(link(f.a, rp.a), link(f.b, rp.b))
  end
where:
  unzip2([]) is pair([],[])
  unzip2([pair(1,2)]) is pair([1], [2])
  unzip2([pair(1,2), pair(3,4)]) is pair([1,3], [2,4])
end

fun<A> list-to-option(l :: List<A>) -> Option<A>:
  cases(List) l:
    | empty => none
    | link(f, _) => some(f)
  end
where:
  list-to-option([]) is none
  list-to-option([1,2]) is some(1)
  list-to-option([3]) is some(3)
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

fun tyshallowequals(t1 :: Type, t2 :: Type) -> Bool:
  doc: "equality only in tags"
  cases(Type) t1:
    | dynType => is-dynType(t2)
    | anyType => is-anyType(t2)
    | nameType(_) => is-nameType(t2)
    | anonType(_) => is-anonType(t2)
    | arrowType(_,_,_) => is-arrowType(t2)
    | methodType(_,_,_,_) => is-methodType(t2)
    | appType(_,_) => is-appType(t2)
    | bigLamType(_,_) => is-bigLamType(t2)
  end
where:
  tyshallowequals(dynType, dynType) is true
  tyshallowequals(nmty("A"), nmty("B")) is true
  tyshallowequals(nmty("A"), dynType) is false
end

fun tycompat(t1 :: Type, t2 :: Type) -> Bool:
  doc: "equality with Dyn and bigLamType"
  cases(Type) t1:
    | dynType => true
    | bigLamType(params, type) =>
      not is-incompatible(tysolve(params, [pair(type, t2)], []))
    | else =>
      cases(Type) t2:
        | dynType => true
        | bigLamType(params, type) =>
          not is-incompatible(tysolve(params, [pair(type, t1)], []))
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
    | bigLamType(params, type) =>
      if params.member(v): false
      else: appears(v, type)
      end
    | dynType => false
    | anyType => false
  end
end

fun replace(v :: Type, nt :: Type, t :: Type) -> Type:
  doc: "replace any occurrence of v with nt in t"
  fun rec-replace(_v :: Type, _nt :: Type, r :: RecordType) -> RecordType:
    cases(RecordType) r:
      | normalRecord(fields) =>
        normalRecord(fields.map(fun(p): pair(p.a, replace(_v,_nt,p.b)) end))
      | moreRecord(fields) =>
        moreRecord(fields.map(fun(p): pair(p.a, replace(_v,_nt,p.b)) end))
    end
  end
  cases(Type) t:
    | nameType(name) => if t == v: nt else: t end
    | anonType(rec) => anonType(rec-replace(v, nt, rec))
    | arrowType(args, ret, rec) =>
      arrowType(args.map(replace(v,nt,_)), replace(v,nt,ret), rec-replace(v,nt, rec))
    | methodType(self, args, ret, rec) =>
      methodType(replace(v,nt,self), args.map(replace(v,nt,_)), replace(v,nt,ret), rec-replace(v,nt, rec))
    | appType(name, args) =>
      appType(name, args.map(replace(v,nt,_)))
    | bigLamType(params, type) =>
      if is-nameType(v) and params.member(v.name): t
      else: bigLamType(params, replace(v, nt, type))
      end
    | dynType => t
    | anyType => t
  end
end

data TySolveRes:
  | allSolved(l :: List<Type>)
  | someSolved(l :: List<Type>)
  | incompatible
end

fun tysolve(vars :: List<String>, _eqs :: List<Pair<Type, Type>>, tys :: List<Type>) -> TySolveRes:
  doc: "Solves for vars using eqs (by constraint generation/elimination) and uses those to substitute into tys.
        If all are not solved for, returns someSolved, where the remaining ones have been replaced with dynType.
        In the case of incompatibility (ie, not possible to solve), returns incompatible.
        This is how we instantiate type parameters through local inference."

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
    fun solve-nested(_params :: List<String>, _t1 :: Type, _t2 :: Type) -> List<Pair<String, Type>>:
      to-rename = _params.filter(vars.member(_))
      not-to-rename = _params.filter(fun(p): not vars.member(p) end)
      # a hack in the true spirit - prefix by equal number _ as the longest identifier in vars.
      # as long as we don't go deep (2 or 3 max), the exponential nature of this shouldn't matter.
      max-len = vars.map(_.length()).foldr(fun(x, m): if x > m: x else: m end end, 0)
      t1 = for fold(acc from _t1, r from to-rename):
        replace(nmty(r), nmty("_".repeat(max-len) + r), acc)
      end
      t2 = for fold(acc from _t2, r from to-rename):
        replace(nmty(r), nmty("_".repeat(max-len) + r), acc)
      end
      params = to-rename.map("_".repeat(max-len) + _) + not-to-rename
      rel-vars = vars.filter(fun(v): appears(v, t1) or appears(v, t2) end)
      cases(TySolveRes) tysolve(params + rel-vars, [pair(t1, t2)], rel-vars.map(nmty)):
        | allSolved(inner-eqs) => zip2(rel-vars, inner-eqs)
        | someSolved(inner-eqs) => zip2(rel-vars, inner-eqs)
        | incompatible => raise(nothing)
      end
    end
    cases(List) eqs:
      | empty => empty
      | link(tp, r) =>
        cases(Pair) tp:
          | pair(t1, t2) =>
            if (t1 == dynType) or (t2 == dynType):
              # dyn gives us no information about constraints.
              congen(r)
            else:
              cases(Type) t1:
                | nameType(n1) =>
                  if vars.member(n1):
                    link(pair(n1, t2), congen(r))
                  else:
                    if is-nameType(t2) and vars.member(t2.name):
                      link(pair(t2.name, t1), congen(r))
                    else if is-dynType(t2) or (is-nameType(t2) and (n1 == t2.name)):
                      congen(r)
                    else if is-bigLamType(t2):
                      solve-nested(t2.params, t2.type, t1)
                    else:
                      raise(nothing)
                    end
                  end
                | anonType(rec1) =>
                  (cases(Type) t2:
                      | anonType(rec2) =>
                        recgen(rec1, rec2)
                      | bigLamType(params, type) => solve-nested(params, type, t1)
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
                    | bigLamType(params, type) => solve-nested(params, type, t1)
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
                    | bigLamType(params, type) => solve-nested(params, type, t1)
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
                    | bigLamType(params, type) => solve-nested(params, type, t1)
                    | else =>
                      if is-nameType(t2) and vars.member(t2.name):
                        link(pair(t2.name, t1), congen(r))
                      else:
                        raise(nothing)
                      end
                  end
                | bigLamType(params, type) => solve-nested(params, type, t2)
                | anyType =>
                  if t2 == anyType:
                    congen(r)
                  else if is-nameType(t2) and vars.member(t2.name):
                    link(pair(t2.name, t1), congen(r))
                  else:
                    raise(nothing)
                  end
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
                          pair(r.a, replace(nmty(a), b, r.b))
                        end
                      end)))
              end
            else:
              raise("tysolve: invariant violated - left side should be var.")
            end
        end
    end
  end

  fun conreplace(sols :: List<Pair<String,Type>>, _tys :: List<Type>) -> TySolveRes:
    replaced = for fold(acc from _tys, sol from sols):
      acc.map(replace(nmty(sol.a), sol.b, _))
    end
    if list.any(fun(x): x end, replaced.map(fun(r): list.any(fun(x): x end, vars.map(appears(_, r))) end)):
      someSolved(for fold(acc from replaced, v from vars):
          acc.map(replace(nmty(v), dynType, _))
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

  tysolve(["U"], [pair(nmty("U"), nmty("Bool")),
      pair(bigLamType(["T"], appty("Foo", [nmty("T")])), appty("Foo", ["String"]))], [nmty("U")])
  is allSolved([nmty("Bool")])

  tysolve(["U", "V"], [
      pair(bigLamType(["T"], appty("Foo", [nmty("T"), nmty("V"), nmty("Bool")])), appty("Foo", ["String", "Number", "U"]))], [nmty("U"), nmty("V")])
  is allSolved([nmty("Bool"), nmty("Number")])

  tysolve(["U"], [pair(bigLamType(["T"], appty("Foo", [nmty("T"), nmty("Bool")])), appty("Foo", ["String", "U"]))], [nmty("U")])
  is allSolved([nmty("Bool")])

  tysolve(["T"], [pair(nmty("T"), nmty("Bool")),
      pair(bigLamType(["T"], appty("Foo", [nmty("T")])), appty("Foo", ["String"]))], [nmty("T")])
  is allSolved([nmty("Bool")])

  tysolve(["T"], [pair(nmty("T"), nmty("Bool")),
      pair(appty("Foo", ["String"]), bigLamType(["T"], appty("Foo", [nmty("T")])))], [nmty("T")])
  is allSolved([nmty("Bool")])

  tysolve([], [pair(nmty("Bool"), nmty("Bool"))], []) is allSolved([])
  tysolve(["T"], [pair(nmty("Bool"), nmty("Bool"))], [nmty("T")]) is someSolved([dynType])
end


data RenameRes:
  | renameRes(params :: List<String>, types :: List<Type>)
end
fun rename-params(_params, types-appear, types-rename):
  doc: "renames any params that appear in types-appear in types-rename"
  # this is a hack - we want a pool of free variables... Assuming enough of these
  # will be free.
  fvs = builtins.string-to-list("ABCDEFGHIJKLMNOPQRSTUVWXYZ").filter(
    fun(v): not list.any(fun(x): x end, types-appear.map(appears(v,_))) end)

  fun h(params, fv-index, new-params, new-types):
    cases(List) params:
      | empty => renameRes(new-params, new-types)
      | link(f, r) =>
        if list.any(fun(x): x end, types-appear.map(appears(f, _))):
          np = fvs.get(fv-index)
          h(r, fv-index + 1, new-params + [np], new-types.map(replace(nmty(f), nmty(np), _)))
        else:
          h(r, fv-index, new-params + [f], new-types)
        end
    end
  end

  h(_params, 0, [], types-rename)
where:
  rename-params(["T"], [nmty("T")], [nmty("T")]) is renameRes(["A"], [nmty("A")])
  rename-params(["T"], [nmty("U")], [nmty("T")]) is renameRes(["T"], [nmty("T")])
  rename-params(["T", "U", "V"], [nmty("U")], [nmty("T"), nmty("U")]) is renameRes(["T", "A", "V"], [nmty("T"), nmty("A")])
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
          add-bindings([pair(name.id, dynType)],
            tc(val)^bind(fun(ty): return([pair(name.id, ty)]) end))
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
    eval(get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [], default-type-env)
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
  bigty = if tparams == []: nmty(tname) else: appty(tname, tparams) end
  boolty = nmty("Bool")
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
      # Without that, we can't typecheck methods of user defined datatypes.
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
  footy = nmty("Foo")
  boolty = nmty("Bool")
  strty = nmty("String")
  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [], [], default-type-env)
  is
  [pair("foo", arrowType([], footy, moreRecord([]))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))]

  eval(get-variant-bindings("Foo", ["T"],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [],[],default-type-env)
  is
  [pair("foo", bigLamType(["T"],arrowType([strty], appty("Foo", ["T"]), moreRecord([])))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))]


  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [],[],[],[],default-type-env)
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
    eval(get-type-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [], [])
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
                              if list.any(is-bigLamType, argsty + [rightty]):
                                # NOTE(dbp 2013-11-17): I do not thing we can use uninstantiated
                                # arguments without losing the simplicity of our inference. All
                                # straightforward instantiations seem like they can be used to break
                                # things.
                                return([])
                              else:
                                return([arrowType(argsty, rightty, moreRecord([]))])
                              end
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
  # TODO(dbp 2013-11-15): Handle arity mismatch somewhere...

  # this is a hack - we want a pool of free variables... Assuming enough of these
  # will be free.
  var tyvars = [] # will be set once we can figure out what are available.
  var varcount = 0
  # TODO(dbp 2013-11-15): Return mismatch if records are not compatible (right now it
  # will either blow up or silently work.)
  fun rec-mismatch(r1 :: RecordType, r2 :: RecordType) -> List<Pair<Type, Type>>:
    list-to-option(
      r1.fields.map(fun(f): mismatch(f.b, map-get(r2, f.a).value) end).filter(is-some).map(_.value)
      )
  end
  fun mismatch(t1 :: Type, t2 :: Type) -> Option<Pair<Type, Type>>:
    doc: "finds the first mismatch between types"
    cases(Type) t1:
      | nameType(name) => if t1 == t2: none else: some(pair(t1, t2)) end
        | anonType(rec) => if is-anonType(t2): rec-mismatch(rec, t2.rec) else: [pair(t1, t2)] end
      | arrowType(args, ret, rec) =>
        if is-arrowType(t2):
          list-to-option((map2(mismatch, args, t2.args) + [mismatch(ret, t2.ret)]).filter(is-some).map(_.value))
        else: some(pair(t1, t2)) end
      | methodType(self, args, ret, rec) =>
        if is-methodType(t2):
          list-to-option(([mismatch(self, t2.self)] + map2(mismatch, args, t2.args) + [mismatch(ret, t2.ret)]).filter(is-some).map(_.value))
        else: some(pair(t1, t2)) end
      | appType(name, args) =>
        if is-appType(t2) and (name == t2.name): list-to-option(map2(mismatch, args, t2.args).filter(is-some).map(_.value))
        else: some(pair(t1, t2)) end
      | bigLamType(params, type) =>
        # TODO(dbp 2013-11-15): Figure out what better we can do in this case.
        if is-bigLamType(t2): mismatch(type, t2.type)
        else: some(pair(t1, t2)) end
        # TODO(dbp 2013-11-15): Not sure if this is right. What does dynType mismatch with?
      | dynType => none
      | anyType => if is-anyType(t2): none else: some(pair(anyType, t2)) end
    end
  end
  fun structural-replace(tyvar :: String, o1 :: Type, t1 :: Type, o2 :: Type, t2 :: Type) -> Pair<Type, Type>:
    doc: "this function stops replacing when it finds t1 <> t2 where t1 and t2 are not o1 and o2 respectively. This is because this is the part of the greedy algorithm that starts with mismatch, which finds the first mismatch."
    sr = structural-replace(tyvar, o1, _, o2, _)
    fun rec-struc-replace(r1, r2):
      fs = r1.fields.map(_.a)
      unzip2(fs.map(fun(f):
          ns = sr(f.b, map-get(r2, f.a).value)
          pair(pair(f.a, ns.a), pair(f.a, ns.b))
        end))
    end
    if (t1 == o1) and (t2 == o2):
      pair(nmty(tyvar), nmty(tyvar))
    else if not tyshallowequals(t1, t2):
      pair(t1, t2)
    else:
      cases(Type) t1:
        | dynType => pair(t1, t2)
        | anyType => pair(t1, t2)
        | nameType(name) => pair(t1, t2)
        | anonType(record) =>
          s = rec-struc-replace(record, t2.record)
          pair(anonType(s.a), anonType(s.b))
        | arrowType(args, ret, record) =>
          ars = unzip2(map2(sr, args, t2.args))
          r = sr(ret, t2.ret)
          rec = rec-struc-replace(record, t2.record)
          pair(arrowType(ars.a, r.a, moreRecord(rec.a)), arrowType(ars.b, r.b, moreRecord(rec.b)))
        | methodType(self, args, ret, record) =>
          s = sr(self, t2.self)
          ars = unzip2(map2(sr, args, t2.args))
          r = sr(ret, t2.ret)
          rec = rec-struc-replace(record, t2.record)
          pair(methodType(s.a, ars.a, r.a, rec.a), methodType(s.b, ars.b, r.b, rec.b))
        | appType(name, args) =>
          aps = unzip2(map2(sr, args, t2.args))
          pair(appType(name, aps.a), appType(t2.name, aps.b))
        | bigLamType(params, type) =>
          # TODO(dbp 2013-11-16): Don't allow shadowing to mess this up.
          p = sr(type, t2.type)
          pair(bigLamType(params, p.a), bigLamType(t2.params, p.b))
      end
    end
  end
  fun replace-pairwise(tyvar :: String, o1 :: Type, ty1 :: List<Type>, o2 :: Type, ty2 :: List<Type>) -> List<Pair<Type, Type>>:
    cases(List) ty1:
      | empty => empty
      | link(f1, r1) =>
        f2 = ty2.first
        r2 = ty2.rest
        link(structural-replace(tyvar, o1, f1, o2, f2), replace-pairwise(tyvar, o1, r1, o2, r2))
    end
  end
  fun match-pairs(existing :: List<Type>, matching :: List<Type>) -> List<Type>:
    cases(List) existing:
      | empty => existing
      | link(f, r) =>
        cases(Option) mismatch(f, matching.first):
          | none => link(f, match-pairs(r, matching.rest))
          | some(mm-ts) =>
            newvar = tyvars.get(varcount)
            varcount := varcount + 1
            updated = unzip2(replace-pairwise(newvar, mm-ts.a, existing, mm-ts.b, matching))
            # NOTE(dbp 2013-11-16): This is generative. What is shrinking is the number of
            # mismatches, enforced by the (hopeful) correctness of mismatch/replace-pairwise.
            match-pairs(updated.a, updated.b)
        end
    end
  end
  fun compute-type(tests :: List<List<Type>>, type :: List<Type>) -> List<Type>:
    cases(List) tests:
      | empty => type
      | link(f, r) =>
        compute-type(r, match-pairs(type, f))
    end
  end
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      get-iifs()^bind(fun(iifs):
          for foldm(fns from iifs, stmt from stmts):
            add-bindings(fns, is-inferred-functions(stmt)^bind(fun(fs):
                  return(fns + fs)
                end))
          end
        end)
    | s_fun(l, name, params, args, ann, doc, body, ck) =>
      find-is-pairs(name, ck)^bind(fun(pairs):
          if pairs <> []:
            fun a2l(t) -> List<Type>: t.args + [t.ret] end
            tylists = pairs.map(a2l)
            tyvars := builtins.string-to-list("TUVWABCDEFGHIJKLMNOPQRSXYZ").filter(
              fun(v): not list.any(fun(x): x end, tylists.map(fun(lst):
                    list.any(fun(x): x end, lst.map(appears(v,_)))
                    end))
              end)
            ct = compute-type(tylists.rest, tylists.first)
            typarams = tyvars.take(varcount).filter(fun(v):
                list.any(fun(x): x end, ct.map(appears(v,_)))
              end)
            type = params-wrap(typarams, arrowType(ct.take(ct.length() - 1), ct.last(), moreRecord([])))
            return([pair(name, type)])
          else:
            return([])
          end
        end)
    | else => return([])
  end
where:
  fun iif-src(src):
    stx = A.parse(src,"anonymous-file", { ["check"]: false}).pre-desugar
    eval(is-inferred-functions(stx.block), [], [], [], default-env, default-type-env)
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

  iif-src("fun f(x): x where: f(10) is 10 f(true) is true end") is
  [pair("f", bigLamType(["T"], arrowType([nmty("T")], nmty("T"), baseRec)))]

  iif-src("fun f(x, y): x where: f(10, 10) is 10 f(true, false) is true end") is
  [pair("f", bigLamType(["T"], arrowType([nmty("T"), nmty("T")], nmty("T"), baseRec)))]

  iif-src("fun f(x, y): x where: f(10, 10) is 10 f(true, 10) is true end") is
  [pair("f", bigLamType(["T"], arrowType([nmty("T"), nmty("Number")], nmty("T"), baseRec)))]

  iif-src("fun f(x, y): x where: f(10, 10) is 10 f(true, 10) is true f('foo', 'bar') is 'foo' end") is
  [pair("f", bigLamType(["U", "V"], arrowType([nmty("U"), nmty("V")], nmty("U"), baseRec)))]

  iif-src("fun f(x, y, c): x where: f(10, true, 10) is 10 f(true, false, 10) is true f('foo', true, 'bar') is 'foo' end") is
  [pair("f", bigLamType(["U", "V"], arrowType([nmty("U"), nmty("Bool"), nmty("V")], nmty("U"), baseRec)))]

  iif-src("fun f(x): x.first where: f([10]) is 10 f(['foo']) is 'foo' end") is
  [pair("f", bigLamType(["T"], arrowType([appty("List", ["T"])], nmty("T"), baseRec)))]
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
  eval(subtype(l, anyType, anyType), [], [], [], [], default-type-env) is true
  numType = nmty("Number")
  eval(subtype(l, numType, anyType), [], [], [], [], default-type-env) is true
  eval(subtype(l, anyType, numType), [], [], [], [], default-type-env) is false

  eval(subtype(l, nmty("Any"), nmty("Any")), [], [], [], [], default-type-env) is true
  eval(subtype(l, numType, nmty("Any")), [], [], [], [], default-type-env) is true
  eval(subtype(l, nmty("Any"), numType), [], [], [], [], default-type-env) is false

  fun recType(flds): anonType(normalRecord(flds)) end

  eval(subtype(l, recType([pair("foo", anyType)]), anyType), [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", anyType)])), [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", numType)])), [], [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType)]), recType([pair("foo", anyType)])), [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([]), recType([pair("foo", numType)])), [], [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType), pair("bar", anyType)]),
      recType([pair("foo", anyType)])), [], [], [], [], default-type-env) is true

  eval(subtype(l, arrowType([], dynType, moreRecord([])),
      arrowType([dynType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([numType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([numType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], anyType, moreRecord([])),
      arrowType([anyType], numType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], numType, moreRecord([])),
      arrowType([anyType], anyType, moreRecord([]))), [], [], [], [], default-type-env) is false

  eval(subtype(l, methodType(dynType, [], dynType, moreRecord([])),
      methodType(dynType, [dynType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is false
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(numType, [numType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is false
  eval(subtype(l, methodType(anyType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], anyType, moreRecord([])),
      methodType(anyType, [anyType], numType, moreRecord([]))), [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], numType, moreRecord([])),
      methodType(anyType, [anyType], anyType, moreRecord([]))), [], [], [], [], default-type-env) is false

  eval(subtype(l, anyType, nmty("Any")), [], [], [], [], default-type-env) is true

  eval(subtype(l, appty("Foo", []), nmty("Any")), [], [], [], [], default-type-env)
  is true
  eval(subtype(l, appty("Foo", []), bigLamType(["T"], appType("Foo", []))), [], [], [], [], default-type-env)
  is false
  eval(subtype(l, appty("Foo", ["String"]), appty("Foo", ["Any"])), [], [], [], [], default-type-env)
  is true
  eval(subtype(l, bigLamType(["T"], appty("Option", ["T"])), bigLamType(["T"], appty("Option", ["T"]))), [], [], [], [], default-type-env)
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
            pair("join-str", app-mty("List", "T", ["String"], appty("List", ["T"]))),
            pair("_plus", app-mty("List", "T", [appty("List", ["T"])], appty("List", ["T"]))),
            pair("push", app-mty("List", "T", [nmty("T")], appty("List", ["T"])))
          ])))),
  pair(nameType("Option"), typeAlias(bigLamType(["T"], appType("Option", [nmty("T")])))),
  pair(bigLamType(["T"], appType("Option", [nmty("T")])), typeNominal(anonType(moreRecord([])))),
  pair(nameType("Nothing"), typeNominal(anonType(normalRecord([]))))
]

default-env = [
  pair("list", anonType(
      moreRecord([
          pair("map", bigLamType(["U", "T"], arrowType([arrowType([nmty("T")], nmty("U"), moreRecord([])), appty("List", ["T"])], appty("List", ["U"]), moreRecord([])))),
          pair("link", bigLamType(["T"], arrowType([nmty("T"), appty("List", ["T"])], appty("List", ["T"]), moreRecord([])))),
          pair("empty", bigLamType(["T"], appType("List", [nmty("T")])))
        ]))),
  pair("builtins", anonType(moreRecord([
          pair("equiv", arrowType([nmty("Any"), nmty("Any")], nmty("Bool"), moreRecord([])))
        ]))),
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
  pair("raise", arrowType([anyType], dynType, moreRecord([]))),
  pair("identical", arrowType([anyType, anyType], nmty("Bool"), moreRecord([]))),
  pair("Racket", dynType),
  pair("List", arrowType([anyType], nmty("Bool"), moreRecord([]))),
  pair("String", arrowType([anyType], nmty("Bool"), moreRecord([]))),
  pair("Function", arrowType([anyType], nmty("Bool"), moreRecord([]))),
  pair("Bool", arrowType([anyType], nmty("Bool"), moreRecord([]))),
  pair("Number", arrowType([anyType], nmty("Bool"), moreRecord([]))),
  pair("Nothing", arrowType([anyType], nmty("Bool"), moreRecord([])))
]

fun tc-main(p, s):
  stx = s^A.parse(p, { ["check"]: false})
  # NOTE(dbp 2013-11-03): This is sort of crummy. Need to get bindings first, for use
  # with inferring functions, but then will do this again when we start type checking...
  bindings = eval(get-bindings(stx.with-types.block), [], [], [], default-env, default-type-env)
  iifs = eval(is-inferred-functions(stx.pre-desugar.block), [], [], [], bindings + default-env, default-type-env)
  run(tc-prog(stx.with-types), [], [], iifs, default-env, default-type-env)
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

data TCBranchRes:
  | branchCompatible(type :: Type)
  | branchIncompatible(types :: List<Type>)
end

fun tc-branches(bs :: List<TCST<Type>>) -> TCST<TCBranchRes>:
  sequence(bs)^bind(fun(_btys):
      fun h(btys, final-tys):
        cases(List) btys:
          | empty => final-tys
          | link(f, r) =>
            if (f == dynType) or (final-tys.member(f)) or list.any(fun(x): x end, final-tys.map(tycompat(_, f))):
              h(r, final-tys)
            else:
              h(r, link(f, final-tys))
            end
        end
      end
      fun blc(t1, t2) -> Bool:
        (not is-bigLamType(t1)) and is-bigLamType(t2)
      end
      fun ble(t1, t2) -> Bool:
        (is-bigLamType(t1) and is-bigLamType(t2)) or ((not is-bigLamType(t1)) and (not is-bigLamType(t2)))
      end
      ftys = h(_btys.sort-by(blc, ble), [])
      fl = ftys.length()
      if _btys.length() == 0:
        # this means there are no branches, so there is no type.
        return(branchCompatible(nmty("Nothing")))
      else if fl == 0:
        # all were dynType
        return(branchCompatible(dynType))
      else if fl == 1:
        return(branchCompatible(ftys.first))
      else:
        return(branchIncompatible(ftys))
      end
    end)
where:
  eval(tc-branches([return(dynType), return(anyType)]), [], [], [], [], default-type-env)
    is branchCompatible(anyType)
  eval(tc-branches([return(dynType), return(anyType),return(nmty("Bool"))]), [], [], [], [], default-type-env)
    is branchIncompatible([anyType, nmty("Bool")])
  eval(tc-branches([return(dynType), return(bigLamType(["T"], appty("Option", ["T"]))),
        return(appty("Option", ["Bool"])), return(appty("Option", ["String"]))]), [], [], [], [], default-type-env)
    is branchIncompatible([appty("Option", ["Bool"]), appty("Option", ["String"])])
  eval(tc-branches([return(dynType), return(bigLamType(["T"], appty("Option", ["T"]))),
        return(bigLamType(["U"], appty("Option", ["U"]))), return(appty("Option", ["String"]))]), [], [], [], [], default-type-env)
    is branchCompatible(appty("Option", ["String"]))

end


################################################################################
# Individual cases of type checker.                                            #
################################################################################

fun tc-let(l :: Loc, name :: A.Bind, val :: A.Expr) -> TCST<Type>:
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
                  # NOTE(dbp 2013-11-16): We need to decide whether to use their type
                  # or our inferred one. For now, we make the simple decision: if their
                  # type contains any blanks, we use ours. This can and probably should
                  # be improved.
                  inferred = list.any(A.is-a_blank, args.map(_.ann) + [ann])
                  if inferred:
                    cases(Type) fty:
                      | arrowType(arganns, ret, rec) =>
                        tc-lam(l1, [], map2(fun(b, a): pair(b.id, a) end, args, arganns), ret, body, typeInferred)
                      | bigLamType(params, type) =>
                        # type is an arrowType
                        tc-lam(l1, params, map2(fun(b, a): pair(b.id, a) end, args, type.args), type.ret, body, typeInferred)
                    end
                  else:
                    tc(val)
                  end
                | else =>
                  # NOTE(dbp 2013-10-21): This is a bizarre case. It means
                  # we no longer understand the desugaring, so we really
                  # should abort and figure our stuff out.
                  raise("tc error: encountered a let binding that should have been a function, but wasn't (at loc " +
                    torepr(l) + ")")
              end
          end
        end)
    end)
end

fun tc-lam(l :: Loc, ps :: List<String>, args :: List<Pair<String,Type>>, ret-ty :: Type, body :: A.Expr, inferred :: TypeInferred) -> TCST<Type>:
  # NOTE(dbp 2013-11-03): Check for type shadowing.
  bind-params(ps,
    add-bindings(args,
      tc(body)^bind(fun(body-ty):
          subtype(l, body-ty, ret-ty)^bind(fun(st):
              if st:
                (if (body-ty == dynType) and (ret-ty <> dynType):
                    add-warning(l, wmsg(warnFunctionBodyDyn(fmty(ret-ty))))
                  else: return(nothing)
                  end)^seq(
                  return(params-wrap(ps, arrowType(args.map(fun(bnd): bnd.b end),
                        ret-ty, moreRecord([]))))
                  )
              else:
                cases(TypeInferred) inferred:
                  | typeNotInferred =>
                    add-error(l,
                      msg(errFunctionAnnIncompatibleReturn(fmty(body-ty), fmty(ret-ty))))^seq(
                      return(dynType))
                  | typeInferred =>
                    add-error(l,
                      msg(errFunctionInferredIncompatibleReturn(fmty(body-ty), fmty(ret-ty))))^seq(
                      return(dynType))
                end
              end
            end)
        end)
      )
    )
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
        | bigLamType(params, ty1) =>
          cases(Type) ty1:
            | arrowType(arg-types, ret-type, rec-type) =>
              if args.length() <> arg-types.length():
                add-error(l,
                  msg(errArityMismatch(arg-types.length(), args.length())))^seq(
                  return(dynType))
              else:
                sequence(args.map(tc))^bind(fun(arg-vals):
                    cases(TySolveRes) tysolve(params, zip2(arg-types, arg-vals), [ret-type]):
                      | allSolved(vs) => return(vs.first)
                      | someSolved(vs) =>
                        # NOTE(dbp 2013-11-09): Add warning - ret type has dynType due to underspecification
                        return(vs.first)
                      | incompatible =>
                        add-error(l, msg(errFunctionArgumentsIncompatible(fmty(ty1), arg-vals.map(fmty))))^seq(return(dynType))
                    end
                  end)
              end
            | dynType => return(dynType)
            | else =>
              add-error(l, msg(errApplyNonFunction(fmty(fn-ty))))^seq(return(dynType))
          end
          # NOTE(dbp 2013-10-16): Not really anything we can do. Odd, but...
        | dynType => return(dynType)
        | else =>
          add-error(l, msg(errApplyNonFunction(fmty(fn-ty))))^seq(return(dynType))
      end
    end)
end

fun tc-if(l, branches, elsebranch) -> TCST<Type>:
  sequence(branches.map(fun(branch):
        tc(branch.test)^bind(fun(ty):
            if tycompat(nmty("Bool"), ty):
              return(nothing)
            else:
              add-error(branch.l, msg(errIfTestNotBool(fmty(ty))))
            end
          end)
      end))^seq(
    tc-branches([tc(elsebranch)] + branches.map(_.body).map(tc))^bind(fun(br):
        cases(TCBranchRes) br:
          | branchIncompatible(tys) => add-error(l, msg(errIfBranchType(tys.map(fmty))))^seq(return(dynType))
          | branchCompatible(ty) => return(ty)
        end
      end))
end

fun tc-bracket(l :: Loc, obj :: A.Expr, field :: A.Expr) -> TCST<Type>:
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
              | none =>
                add-error(l, msg(errFieldNotFound(s)))^seq(return(dynType))
              | some(ty) =>
                return(method-apply(ty))
            end
          | moreRecord(fields) =>
            cases(Option) map-get(fields, s):
              | none =>
                return(dynType)
              | some(ty) => return(method-apply(ty))
            end
        end
      end
      var loop-point = nothing
      fun record-type-lookup(type):
        get-type-env()^bind(fun(type-env):
            cases(Option) map-get(type-env, type):
              | none => add-error(l, msg(errTypeNotDefined(fmty(type))))^seq(return(dynType))
              | some(recordbind) =>
                cases(Type) recordbind.type:
                  | anonType(record) => record-lookup(record)
                  | anyType => return(dynType)
                  | dynType => return(dynType)
                  | appType(_,_,_) => return(dynType)
                  | nameType(_) =>
                    if (not Nothing(loop-point)) and identical(loop-point, recordbind.type):
                      # don't go into an infinite loop.
                      return(dynType)
                    else:
                      loop-point := recordbind.type
                      record-type-lookup(recordbind.type)
                    end
                end
            end
          end)
      end
      fun rec-loo-help(obj-ty):
        cases(Type) obj-ty:
          | dynType => return(dynType)
          | anyType => return(dynType)
          | appType(name,args) =>
            # NOTE(dbp 2013-11-09): Look up general type in type env.
            get-type-env()^bind(fun(type-env):
                cases(Option) map-get(type-env, nmty(name)):
                  | none => add-error(l, msg(errTypeNotDefined(fmty(nmty(name)))))^seq(return(dynType))
                  | some(typebind) =>
                    cases(Type) typebind.type:
                      | bigLamType(params, ptype) =>
                        record-type-lookup(typebind.type)^bind(fun(pty):
                            cases(TySolveRes) tysolve(params, [pair(ptype, obj-ty)], [pty]):
                              | allSolved(vs) => return(vs.first)
                              | someSolved(vs) => return(vs.first)
                              | incompatible =>
                                add-error(l, msg(errAppTypeNotWellFormed(fmty(obj-ty), fmty(typebind.type))))
                                  ^seq(return(dynType))
                            end
                          end)
                      | else => raise("tc: found an appType that didn't map to a bigLamType in the type env. This violates a constraint, aborting.")
                    end
                end
              end)
          | anonType(record) => record-lookup(record)
          | nameType(_) => record-type-lookup(obj-ty)
          | bigLamType(params,t) =>
            record-type-lookup(obj-ty)^bind(fun(r):
                if list.any(fun(x): x end, params.map(appears(_, r))):
                  return(bigLamType(params, r))
                else:
                  return(r)
                end
              end)
        end
      end
      tc(obj)^bind(rec-loo-help)
    | else =>
      # TODO(dbp 2013-10-21): Actually type check field to see if
      # it is a String or Dyn
      return(dynType)
  end
end

fun tc-cases(l :: Loc, _type :: A.Ann, val :: A.Expr, branches :: List<A.CasesBranch>) -> TCST<Type>:
  fun branch-check(params :: List<String>, base :: Type, variant :: Type, branch :: A.CasesBranch) -> TCST<Type>:
    if is-incompatible(tysolve(params, [pair(base, variant)], [])):
      add-error(branch.l,
        msg(errCasesBranchInvalidVariant(fmty(base), branch.name, fmty(variant)))
        )^seq(return(dynType))
    else:
      tc(branch.body)
    end
  end
  get-type(_type)^bind(
    fun(type):
      tc(val)^bind(
        fun(val-ty):
          if not tycompat(type, val-ty):
            add-error(l,
              msg(errCasesValueBadType(fmty(type), fmty(val-ty)))
              )^seq(return(dynType))
          else:
            get-env()^bind(
              fun(env):
                tc-branches(branches.map(fun(branch):
                      if branch.name == "%else":
                        tc(branch.body)
                      else:
                        cases(Option) map-get(env, branch.name):
                          | none => add-error(branch.l,
                              msg(errCasesBranchInvalidVariant(fmty(type), branch.name, "Unknown"))
                              )^seq(return(dynType))
                          | some(ty) =>
                            cases(Type) ty:
                              | arrowType(args, ret, rec) =>
                                if args.length() <> branch.args.length():
                                  add-error(branch.l,
                                    msg(errCasesPatternNumberFields(branch.name, args.length(), branch.args.length()))
                                    )^seq(return(dynType))
                                else:
                                  add-bindings(for map2(bnd from branch.args,
                                        argty from args):
                                      pair(bnd.id, argty)
                                    end,
                                    branch-check([], type, ret, branch))
                                end
                              | nameType(_) =>
                                if branch.args.length() <> 0:
                                  add-error(branch.l,
                                    msg(errCasesPatternNumberFields(branch.name, 0, branch.args.length()))
                                    )^seq(return(dynType))
                                else:
                                  branch-check([], type, ty, branch)
                                end
                              | appType(_,_) =>
                                if branch.args.length() <> 0:
                                  add-error(branch.l,
                                    msg(errCasesPatternNumberFields(branch.name, 0, branch.args.length()))
                                    )^seq(return(dynType))
                                else:
                                  branch-check([], type, ty, branch)
                                end
                              | bigLamType(params, ty1) =>
                                cases(Type) ty1:
                                  | arrowType(args, ret, rec) =>
                                    # rename any params that appear in type. this needs to happen in ret and args.
                                    cases(RenameRes) rename-params(params, [type], [arrowType(args, ret, moreRecord([]))]):
                                      | renameRes(new-params, new-types) =>
                                        new-arr = new-types.first
                                        solved = tysolve(new-params, [pair(new-arr.ret, type)], new-arr.args)
                                        cases(TySolveRes) solved:
                                          | incompatible =>
                                            add-error(branch.l,
                                              msg(errCasesBranchInvalidVariant(fmty(type), branch.name, fmty(ty)))
                                              )^seq(return(dynType))
                                          | else =>
                                            add-bindings(for map2(bnd from branch.args,
                                                  argty from solved.l):
                                                pair(bnd.id, argty)
                                              end,
                                              tc(branch.body))
                                        end
                                    end
                                  | nameType(_) =>
                                    if branch.args.length() <> 0:
                                      add-error(branch.l,
                                        msg(errCasesPatternNumberFields(branch.name, 0, branch.args.length()))
                                        )^seq(return(dynType))
                                    else:
                                      branch-check(params, type, ty1, branch)
                                    end
                                  | appType(_, _) =>
                                    if branch.args.length() <> 0:
                                      add-error(branch.l,
                                        msg(errCasesPatternNumberFields(branch.name, 0, branch.args.length()))
                                        )^seq(return(dynType))
                                    else:
                                      branch-check(params, type, ty1, branch)
                                    end
                                  | else =>
                                    add-error(branch.l,
                                      msg(errCasesBranchInvalidVariant(fmty(type), branch.name, fmty(ty)))
                                      )^seq(return(dynType))
                                end
                              | else =>
                                add-error(branch.l,
                                  msg(errCasesBranchInvalidVariant(fmty(type), branch.name, fmty(ty)))
                                  )^seq(return(dynType))
                            end
                        end
                      end
                    end))^bind(fun(branchres):
                    cases(TCBranchRes) branchres:
                      | branchIncompatible(tys) =>
                        add-error(l,
                          msg(errCasesBranchType(tys.map(fmty)))
                          )^seq(return(dynType))
                      | branchCompatible(ty) => return(ty)
                    end
                  end)
              end)
          end
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
                | s_block(l, stmts) =>
                  sequence(stmts.map(tc))^bind(
                    fun(tys):
                      return(if tys == []: nmty("Nothing") else: tys.last() end)
                    end)
                | s_user_block(l, block) => tc(block)
                  # NOTE(dbp 2013-11-10): As of now, the type system does not know about mutation,
                  # so vars look like lets.
                | s_var(l, name, val) => tc-let(l, name, val)
                | s_let(l, name, val) => tc-let(l, name, val)
                | s_assign(l, id, val) => return(dynType)
                | s_if_else(l, branches, elsebranch) => tc-if(l, branches, elsebranch)
                | s_try(l, body, id, _except) => tc(body)^seq(add-bindings([pair(id.id, id.ann)], tc(_except)))
                | s_lam(l, ps, args, ann, doc, body, ck) =>
                  bind-params(ps, sequence(args.map(fun(b): get-type(b.ann)^bind(fun(t): return(pair(b.id, t)) end) end)))^bind(fun(argpairs):
                      bind-params(ps, get-type(ann))^bind(fun(ret-ty):
                          tc-lam(l, ps, argpairs, ret-ty, body, typeNotInferred)
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
                | s_bracket(l, obj, field) => tc-bracket(l, obj, field)
                | s_colon_bracket(l, obj, field) => return(dynType)
                | s_datatype(l, name, params, variants, check) =>
                  # NOTE(dbp 2013-10-30): Should statements have type nothing?
                  return(nmty("Nothing"))
                | s_cases(l, type, val, branches) => tc-cases(l, type, val, branches)
                | s_cases_else(l, type, val, branches, _else) =>
                  tc-cases(l, type, val, branches + [A.s_cases_branch(_else.l, "%else", [], _else)])
                  # NOTE(dbp 2013-11-05): Since we type check
                  # pre-desugar code inside 'is' tests for inference, we need
                  # any ast nodes that could appear there (in theory, any surface syntax...)
                | s_list(l, values) =>
                  # NOTE(dbp 2013-11-16): I don't want to re-implement all the logic that
                  # makes desugared lists work, so I'm just going to manually desugar and
                  # then typecheck.
                  tc(values.foldr(fun(v, rst): A.s_app(l, A.s_id(l, "link"), [v, rst]) end, A.s_id(l, "empty")))
                | else => raise("tc: no case matched for: " + torepr(ast))
              end
              )
          end
          )
        )
    end
    )
where:
  fun tc-src(src):
    stx = A.parse(src,"anonymous-file", { ["check"]: false}).with-types
    eval(tc(stx.block), [], [], [], default-env, default-type-env)
  end
  fun tc-stx(stx):
    eval(tc(stx), [], [], [], default-env, default-type-env)
  end

  tc-src("1") is nmty("Number")
  tc-src("[1]") is appty("List", ["Number"])
  tc-src("[1,2,3]") is appty("List", ["Number"])
  tc-stx(A.s_list(dummy-loc, [A.s_num(dummy-loc, 1)])) is appty("List", ["Number"])
  tc-stx(A.s_list(dummy-loc, [A.s_num(dummy-loc, 1), A.s_num(dummy-loc, 2)])) is appty("List", ["Number"])
end
