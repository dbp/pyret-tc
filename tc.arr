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
# benefit from inference on earlier ones.
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
end

data TypeInferred:
  | typeInferred
  | typeNotInferred
end

data TypeBinding:
  | typeAlias(type :: Type)
  | typeNominal(type :: Type)
end

# NOTE(dbp 2013-12-04): The following two used for checking cases().
data DataDef:
  | dataDef(name :: String, params :: List<String>, constructors :: List<DataConstructor>)
end
data DataConstructor:
  | dataConstructor(name :: String, args :: List<Type>)
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
      datatypes :: List<Pair<String, DataDef>>,
      env :: List<Pair<String, Type>>,
      type-env :: List<Pair<String, TypeBinding>>
      )
end

# NOTE(dbp 2013-11-02): The type we want is a parametric alias for an
# S -> Pair<V,S> function, where S is (errors, iifs, env, type-env)
TCST = Function

# First the fundamental monad functions
fun return(v):
  fun(er,w,i,dt,e,t): tcst(v,er,w,i,dt,e,t) end
end
fun bind(mv, mf):
  fun(er,w,i,dt,e,t):
    p = mv(er,w,i,dt,e,t)
    mf(p.value)(p.errors,p.warnings,p.iifs,p.datatypes,p.env,p.type-env)
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
  fun(er,w,i,dt,e,t):
    tcst(er,er,w,i,dt,e,t)
  end
end
fun get-warnings():
  fun(er,w,i,dt,e,t):
    tcst(w,er,w,i,dt,e,t)
  end
end
fun get-iifs():
  fun(er,w,i,dt,e,t):
    tcst(i,er,w,i,dt,e,t)
  end
end
fun get-datatypes():
  fun(er,w,i,dt,e,t):
    tcst(dt,er,w,i,dt,e,t)
  end
end
fun get-env():
  fun(er,w,i,dt,e,t):
    tcst(e,er,w,i,dt,e,t)
  end
end
fun get-type-env():
  fun(er,w,i,dt,e,t):
    tcst(t,er,w,i,dt,e,t)
  end
end
fun put-errors(errors):
  fun(er,w,i,dt,e,t):
    tcst(nothing,errors,w,i,dt,e,t)
  end
end
fun put-warnings(warnings):
  fun(er,w,i,dt,e,t):
    tcst(nothing,er,warnings,i,dt,e,t)
  end
end
fun put-iifs(iifs):
  fun(er,w,i,dt,e,t):
    tcst(nothing,er,w,iifs,dt,e,t)
  end
end
fun put-datatypes(datatypes):
  fun(er,w,i,dt,e,t):
    tcst(nothing,er,w,i,datatypes,e,t)
  end
end
fun put-env(env):
  fun(er,w,i,dt,e,t):
    tcst(nothing,er,w,i,dt,env,t)
  end
end
fun put-type-env(type-env):
  fun(er,w,i,dt,e,t):
    tcst(nothing,er,w,i,dt,e,type-env)
  end
end
fun run(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env)
end
fun eval(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).value
end
fun exec-errors(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).errors
end
fun exec-warns(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).warnings
end
fun exec-iifs(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).iifs
end
fun exec-datatypes(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).datatypes
end
fun exec-env(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).type-env
end
fun exec-type-env(st-prog, errs, warns, iifs, datatypes, env, type-env):
  st-prog(errs,warns,iifs,datatypes,env,type-env).type-env
end

# And finally, application specific actions (note that errors are
# threaded, binds, datatypes, and types are not.)
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
fun add-datatypes(datatypes, mv):
  get-datatypes()^bind(fun(old-dt):
      put-datatypes(datatypes + old-dt)^seq(
        mv^bind(fun(val):
            put-datatypes(old-dt)^seq(
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
    [], [], [], [], [], []
    ) is "hello"
  exec-errors(
    add-error("l1", "error 1")^seq(add-error("l2", "error 2"))
      ^seq(return("hello")),
    [], [], [], [], [], []
    ) is [pair("l1","error 1"), pair("l2","error 2")]
  exec-env(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], [], [], []
    ) is []
  eval(
    add-bindings([pair("a", "T")], get-env()),
    [], [], [], [], [], []
    ) is [pair("a", "T")]
  eval(
    add-datatypes([pair("D", dataDef("D", [], []))], get-datatypes()),
    [], [], [], [], [], []
    ) is [pair("D", dataDef("D", [], []))]
end

eval-default = eval(_, [], [], [], default-datatypes, default-env, default-type-env)


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
  | errApplyUninstantiatedFunction(fnty) with: tostring(self):
      "Can not apply function with type " + fmty(self.fnty) + " without explicit type parameters."
    end
  | errParamArityMismatch(expected, given) with: tostring(self):
      "Function applied with the wrong number of type parameters. Expected " + tostring(self.expected) + " but was applied with " + tostring(self.given) + "."
    end
  | errInstantiateArityMismatch(type, expected, given) with: tostring(self):
      "Type " + fmty(self.type) + " instantiated with the wrong number of type parameters. Expected " + tostring(self.expected) + " but was applied with " + tostring(self.given) + "."
    end
  | errInstantiateNonParametric(type, params) with: tostring(self):
      "Unable to instantiate type " + fmty(self.type) + " with parameters <" + self.params.map(fmty).join-str(", ") + "> - it is not a parametric type."
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
  | errCasesInvalidType(given) with: tostring(self):
      "Type in cases is not a valid datatype: " + fmty(self.given) + "."
    end
  | errCasesMalformedType(expected, given) with: tostring(self):
      "Data type in cases expression is not well formed. Was " + fmty(self.given) + ", but should have been of form " + fmty(self.expected) + "."
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
      "All branches of a cases expression must evaluate to the same type. Found branches with incompatible types: " + self.types.join-str(", ") + "."
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
      "Function with type " + fmty(self.fnty) + " not compatible with arguments " + self.arg-tys.map(fmty).join-str(", ") + "."
    end
  | errAppTypeNotWellFormed(inst, gen) with: tostring(self):
      "Type " + self.inst + " is not a well-formed instance of the type " + self.gen + "."
    end

  | errUnification(t1, l1, t2, l2) with: tostring(self):
      "During inference, a unification error occurred. Could not match types: " + fmterm(self.t1) + " and " +  fmterm(self.t2) + " (at " + torepr(self.l1) + " and " + torepr(self.l1) + " respectively)."
    end
end

data TCWarning:
  | warnFunctionBodyDyn(retty) with: tostring(self):
      "Function body had " + self.retty + " specified as a return type, but type checker found Dyn*."
    end
  | warnInferredTypeParametersIncomplete(typarams) with: tostring(self):
      "Failed to infer all parameters for function application. Inferred types: " + self.typarams.map(fmty).join-str(", ") + "."
    end
  | warnBindingDyn(id, type) with: tostring(self):
      "'" + self.id + "' had " + fmty(self.type) + " specified as type, but type checker found Dyn*."
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
    | methodType(self, args, ret, rec) => fmarrow([], [self] + args, ret)
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

fun<T, U> chain(o :: Option<T>, f :: (T -> Option<U>)) -> Option<U>:
  cases(Option<T>) o:
    | none => none
    | some(t) => f(t)
  end
end

fun<T> all-options(o :: List<Option<T>>) -> Option<List<T>>:
  cases(List<Option<T>>) o:
    | empty => some([])
    | link(f, r) =>
      cases(Option<T>) f:
        | none => none
        | some(t) =>
          cases(Option<T>) all-options(r):
            | none => none
            | some(l) => some(t^link(l))
          end
      end
  end
where:
  all-options([]) is some([])
  all-options([some(1), some(2)]) is some([1,2])
  all-options([none]) is none
  all-options([some(1), some(2), none, some(3)]) is none
end

fun<T> cat-options(os :: List<Option<T>>) -> List<T>:
  cases(List<Option<T>>) os:
    | empty => []
    | link(f, r) =>
      cases(Option<T>) f:
        | none => cat-options(r)
        | some(t) => t^link(cat-options(r))
      end
  end
where:
  cat-options([]) is []
  cat-options([none]) is []
  cat-options([some(1), none]) is [1]
  cat-options([some(1), none, some(2), none]) is [1,2]
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

fun arrty(args :: List, ret) -> Type:
  fun s2t(x): if String(x): nmty(x) else: x end end
  arrowType(args.map(s2t), s2t(ret), moreRecord([]))
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

fun tydyneq(t1 :: Type, t2 :: Type) -> Bool:
  doc: "equality that allows either side to be Dyn"
  cases(Type) t1:
    | dynType => true
    | else =>
      cases(Type) t2:
        | dynType => true
        | else => t1 == t2
      end
  end
end

fun tycompat(t1 :: Type, t2 :: Type) -> Bool:
  doc: "equality with Dyn and bigLamType"
  cases(Type) t1:
    | dynType => true
    | bigLamType(params, type) =>
      not is-incompatible(tysolve(params, [pair(type, rename-params(params, params.map(nmty), [t2]).types.first)], []))
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

# NOTE(dbp 2013-12-02): I may regret this... but since the ast needs anns, I need to convert from
# types back to anns in inference.
fun unget-type(type :: Type, l :: Loc) -> A.Ann:
  cases(Type) type:
    | dynType => A.a_blank
    | anyType => A.a_any
    | nameType(name) => A.a_name(l, name)
    | anonType(record) => A.a_record(l, record.fields.map(fun(p): A.a_field(l, p.a, unget-type(p.b, l)) end))
    | arrowType(args, ret, _) => A.a_arrow(l, args.map(unget-type(_, l)), unget-type(ret, l))
    | methodType(_, _, _) => raise("unget-type: don't know how to turn method types into annotations: " + fmty(type) + " with loc " + torepr(l))
    | appType(name, args) => A.a_app(l, A.a_name(l, name), args.map(unget-type(_, l)))
    | bigLamType(_, _) => raise("unget-type: don't know how to turn bigLamType types into annotations: " + fmty(type) + " with loc " + torepr(l))

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
                  cases(Type) t2:
                    | anonType(rec2) =>
                      recgen(rec1, rec2) + congen(r)
                    | bigLamType(params, type) => solve-nested(params, type, t1) + congen(r)
                    | nameType(n2) =>
                      if vars.member(n2):
                        link(pair(n2, t1), congen(r))
                      else:
                        raise(nothing)
                      end
                    | else => raise(nothing)
                  end
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
                    | nameType(n2) =>
                      if vars.member(n2):
                        link(pair(n2, t1), congen(r))
                      else:
                        raise(nothing)
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
                    | bigLamType(params, type) => solve-nested(params, type, t1)
                    | nameType(n2) =>
                      if vars.member(n2):
                        link(pair(n2, t1), congen(r))
                      else:
                        raise(nothing)
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
                    | bigLamType(params, type) => solve-nested(params, type, t1)
                    | nameType(n2) =>
                      if vars.member(n2):
                        link(pair(n2, t1), congen(r))
                      else:
                        raise(nothing)
                      end
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

  tysolve(["T"], [pair(appty("Option", [anonType(normalRecord([pair("in", nmty("Number"))]))]),
                       appty("Option", ["T"]))], [nmty("T")]) is allSolved([anonType(normalRecord([pair("in", nmty("Number"))]))])
end


data RenameRes:
  | renameRes(params :: List<String>, types :: List<Type>)
end
fun rename-params(_params :: List<String>, types-appear :: List<Type>, types-rename :: List<Type>):
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

fun get-bindings(ast :: A.Expr) -> TCST<Pair<List<Pair<String, Type>>, List<Pair<String, DataDef>>>>:
  doc: "This function implements letrec behavior."
  fun name-val-binds(name, val):
    if A.is-a_blank(name.ann):
      cases(A.Expr) val:
        | s_lam(l1, ps, args, ann, doc, body, ck) =>
          bind-params(ps,
            sequence(args.map(fun(b): get-type(b.ann) end))^bind(fun(arg-tys):
                get-type(ann)^bind(fun(ret-ty):
                    return(pair([pair(name.id, params-wrap(ps, arrowType(arg-tys, ret-ty, moreRecord([]))))], []))
                  end)
              end)
            )
        | else =>
          # NOTE(dbp 2013-11-07): This seems buggy - we want to type check
          # it if it is something simple (like a number, string, application),
          # but not if it can have things like functions in it.
          add-bindings([pair(name.id, dynType)],
            tc(val)^bind(fun(ty): return(pair([pair(name.id, ty)], [])) end))
      end
    else:
      get-type(name.ann)^bind(fun(ty): return(pair([pair(name.id, ty)], [])) end)
    end
  end
  cases(A.Expr) ast:
    | s_block(l, stmts) =>
      get-env()^bind(fun(start-env):
          get-datatypes()^bind(fun(start-dt):
              for foldm(cur from pair([], []), stmt from stmts):
                get-bindings(stmt)^bind(fun(new-binds):
                  put-env(new-binds.a + cur.a + start-env)
                  ^seq(put-datatypes(new-binds.b + cur.b + start-dt))
                  ^seq(return(pair(new-binds.a + cur.a, new-binds.b + cur.b))) end)
              end
            end)
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
        sequence(variants.map(get-variant-bindings(name, params, _)))^bind(fun(_vbs):
            vbs = unzip2(_vbs)
            return(pair(vbs.a^concat() + [pair(name, params-wrap(params, arrowType([anyType], nmty("Bool"), moreRecord([]))))], [pair(name, dataDef(name, params, vbs.b^concat()))]))
          end)
        )
    | else => return(pair([], []))
  end
where:
  fun gb-src(src):
    eval(get-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [], [], default-type-env)
  end
  gb-src("x = 2") is pair([pair("x", nmty("Number"))], [])
  gb-src("x = 2 y = x") is pair([ pair("y", nmty("Number")),
      pair("x", nmty("Number"))], [])
end

fun get-variant-bindings(tname :: String, tparams :: List<String>, variant :: A.Variant(fun(v):
                                     A.is-s_datatype_variant(v) or
                                     A.is-s_datatype_singleton_variant(v) end)) ->
    TCST<Pair<List<Pair<String, Type>>>, List<DataConstructor>>:
  bigty = if tparams == []: nmty(tname) else: appty(tname, tparams) end
  boolty = nmty("Bool")
  fun get-member-type(m): get-type(m.bind.ann) end
  cases(A.Variant) variant:
      # NOTE(dbp 2013-10-30): Should type check constructor here, get methods/fields.
      # Without that, we can't typecheck methods of user defined datatypes.
    | s_datatype_variant(l, vname, members, constr) =>
      sequence(members.map(get-member-type))^bind(fun(memtys):
          return(pair([pair(vname, params-wrap(tparams, arrowType(memtys, bigty, moreRecord([])))),
              pair("is-" + vname, arrowType([anyType], boolty, moreRecord([])))],
              [dataConstructor(vname, memtys)]))
        end)
    | s_datatype_singleton_variant(l, vname, constr) =>
      return(pair([pair(vname, bigty),
          pair("is-" + vname, arrowType([anyType], boolty, moreRecord([])))],
          [dataConstructor(vname, [])]))
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
    [], [], [], [], [], default-type-env)
  is
  pair([pair("foo", arrowType([], footy, moreRecord([]))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))],
    [dataConstructor("foo", [])])

  eval(get-variant-bindings("Foo", ["T"],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal", A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String")))],
      A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [], [], [],[],[],default-type-env)
  is
  pair(
    [pair("foo", bigLamType(["T"],arrowType([strty], appty("Foo", ["T"]), moreRecord([])))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))],
    [dataConstructor("foo", [strty])])


  eval(get-variant-bindings("Foo", [],
    A.s_datatype_variant(dummy-loc, "foo",
    [A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "a", A.a_name(dummy-loc, "String"))),
    A.s_variant_member(dummy-loc, "normal",
        A.s_bind(dummy-loc, "b", A.a_name(dummy-loc, "Bool")))],
    A.s_datatype_constructor(dummy-loc, "self", A.s_id(dummy-loc, "self")))),
    [],[],[],[],[], default-type-env)
  is
  pair(
    [pair("foo", arrowType([strty, boolty], footy, moreRecord([]))),
    pair("is-foo", arrowType([anyType], boolty, moreRecord([])))],
    [dataConstructor("foo", [strty, boolty])])
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
    eval(get-type-bindings(A.parse(src,"anonymous-file", { ["check"]: false}).with-types.block), [], [], [], [], [], [])
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
      | s_check_test(_, op, _l, r) =>
        if op == "opis":
          # NOTE(dbp 2013-10-21): Really simple for now - only if it
          # is of form funname(args) is bar.
          infer(_l)^bind(fun(l):
              cases(A.Expr) l:
                | s_app(l1, fn, args) =>
                  cases(A.Expr) fn:
                    | s_id(l2, fname) =>
                      if fname == name:
                        infer(r)^bind(tc-standalone)^bind(fun(rightty):
                            sequence(args.map(tc-standalone))^bind(fun(argsty):
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
            end)
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
    eval(is-inferred-functions(stx.block), [], [], [], default-datatypes, default-env, default-type-env)
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
  eval(subtype(l, anyType, anyType), [], [], [], [], [], default-type-env) is true
  numType = nmty("Number")
  eval(subtype(l, numType, anyType), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, anyType, numType), [], [], [], [], [], default-type-env) is false

  eval(subtype(l, nmty("Any"), nmty("Any")), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, numType, nmty("Any")), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, nmty("Any"), numType), [], [], [], [], [], default-type-env) is false

  fun recType(flds): anonType(normalRecord(flds)) end

  eval(subtype(l, recType([pair("foo", anyType)]), anyType), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", anyType)])), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([pair("foo", anyType)]), recType([pair("foo", numType)])), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType)]), recType([pair("foo", anyType)])), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, recType([]), recType([pair("foo", numType)])), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, recType([pair("foo", numType), pair("bar", anyType)]),
      recType([pair("foo", anyType)])), [], [], [], [], [], default-type-env) is true

  eval(subtype(l, arrowType([], dynType, moreRecord([])),
      arrowType([dynType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([numType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([numType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, arrowType([anyType], dynType, moreRecord([])),
      arrowType([anyType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], anyType, moreRecord([])),
      arrowType([anyType], numType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, arrowType([anyType], numType, moreRecord([])),
      arrowType([anyType], anyType, moreRecord([]))), [], [], [], [], [], default-type-env) is false

  eval(subtype(l, methodType(dynType, [], dynType, moreRecord([])),
      methodType(dynType, [dynType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], dynType, moreRecord([])),
      methodType(numType, [numType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is false
  eval(subtype(l, methodType(anyType, [anyType], dynType, moreRecord([])),
      methodType(anyType, [anyType], dynType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], anyType, moreRecord([])),
      methodType(anyType, [anyType], numType, moreRecord([]))), [], [], [], [], [], default-type-env) is true
  eval(subtype(l, methodType(numType, [anyType], numType, moreRecord([])),
      methodType(anyType, [anyType], anyType, moreRecord([]))), [], [], [], [], [], default-type-env) is false

  eval(subtype(l, anyType, nmty("Any")), [], [], [], [], [], default-type-env) is true

  eval(subtype(l, appty("Foo", []), nmty("Any")), [], [], [], [], [], default-type-env)
  is true
  eval(subtype(l, appty("Foo", []), bigLamType(["T"], appType("Foo", []))), [], [], [], [], [], default-type-env)
  is false
  eval(subtype(l, appty("Foo", ["String"]), appty("Foo", ["Any"])), [], [], [], [], [], default-type-env)
  is true
  eval(subtype(l, bigLamType(["T"], appty("Option", ["T"])), bigLamType(["T"], appty("Option", ["T"]))), [], [], [], [], [], default-type-env)
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
  pair(nameType("Array"), typeAlias(bigLamType(["T"],appType("Array", [nmty("T")])))),
  pair(bigLamType(["T"],appType("Array", [nmty("T")])),
    typeNominal(anonType(normalRecord([
            pair("_equals", app-mty("Array", "T", ["Any"], "Bool")),
            pair("eq", app-mty("Array", "T", ["Any"], "Bool")),
            pair("_torepr", app-mty("Array", "T", [], "String")),
            pair("tostring", app-mty("Array", "T", [], "String")),
            pair("get", app-mty("Array", "T", ["Number"], nmty("T"))),
            pair("set", app-mty("Array", "T", ["Number", nmty("T")], appty("Array", ["T"]))),
            pair("to-list", app-mty("Array", "T", [], appty("List", ["T"]))),
            pair("length", app-mty("Array", "T", [], "Number"))
          ])))),
  pair(nameType("Option"), typeAlias(bigLamType(["T"], appType("Option", [nmty("T")])))),
  pair(bigLamType(["T"], appType("Option", [nmty("T")])), typeNominal(anonType(moreRecord([])))),
  pair(nameType("Set"), typeAlias(bigLamType(["T"], appType("Set", [nmty("T")])))),
  pair(bigLamType(["T"], appType("Set", [nmty("T")])), typeNominal(anonType(moreRecord([])))),
  pair(nameType("Nothing"), typeNominal(anonType(normalRecord([]))))
]

default-datatypes = [
  pair("List", dataDef("List", ["T"], [dataConstructor("empty", []), dataConstructor("link", [nmty("T"), appty("List", ["T"])])])),
  pair("Option", dataDef("Option", ["T"], [dataConstructor("none", []), dataConstructor("some", [nmty("T")])]))
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
  pair("checkers", anonType(moreRecord([]))),
  pair("option", anonType(moreRecord([]))),
  pair("cs173", anonType(moreRecord([]))),

  pair("link", bigLamType(["T"], arrowType([nmty("T"), appty("List", ["T"])], appty("List", ["T"]), moreRecord([])))),
  pair("empty", bigLamType(["T"], appType("List", [nmty("T")]))),
  pair("is-link", arrty([anyType], "Bool")),
  pair("is-empty", arrty([anyType], "Bool")),
  pair("nothing", nmty("Nothing")),
  pair("some", bigLamType(["T"], arrowType([nmty("T")], appty("Option", ["T"]), moreRecord([])))),
  pair("none", bigLamType(["T"], appType("Option", [nmty("T")]))),
  pair("is-some", arrty([anyType], "Bool")),
  pair("is-none", arrty([anyType], "Bool")),
  pair("true", nmty("Bool")),
  pair("false", nmty("Bool")),
  pair("print", arrowType([anyType], nmty("Nothing"), moreRecord([]))),
  pair("tostring", arrowType([anyType], nmty("String"), moreRecord([]))),
  pair("torepr", arrowType([anyType], nmty("String"), moreRecord([]))),
  pair("map", bigLamType(["U", "T"], arrty([arrty(["T"], "U"), appty("List", ["T"])], appty("List", ["U"])))),
  pair("filter", bigLamType(["T"], arrty([arrty(["T"], "Bool"), appty("List", ["T"])], appty("List", ["T"])))),
  pair("range", arrty(["Number", "Number"], appty("List", ["Number"]))),
  pair("range-by", arrty(["Number", "Number", "Number"], appty("List", ["Number"]))),
  pair("repeat", bigLamType(["T"], arrty(["Number", "T"], appty("List", ["T"])))),
  pair("partition", bigLamType(["T"], arrty([arrty(["T"], "Bool"), appty("List", ["T"])], appty("List", ["T"])))),
  pair("any", bigLamType(["T"], arrty([arrty(["T"], "Bool"), appty("List", ["T"])], "Bool"))),
  pair("find", bigLamType(["T"], arrty([arrty(["T"], "Bool"), appty("List", ["T"])], appty("Option", ["T"])))),
  pair("map2", dynType),
  pair("map3", dynType),
  pair("map4", dynType),
  pair("map_n", dynType),
  pair("map2_n", dynType),
  pair("map3_n", dynType),
  pair("map4_n", dynType),
  pair("each", bigLamType(["T"], arrty([arrty(["T"], "Nothing"), appty("List", ["T"])], "Nothing"))),
  pair("each2", dynType),
  pair("each3", dynType),
  pair("each4", dynType),
  pair("each_n", dynType),
  pair("each2_n", dynType),
  pair("each3_n", dynType),
  pair("each4_n", dynType),
  pair("fold", bigLamType(["U", "T"], arrty([arrty(["U", "T"], "U"), "U", appty("List", ["T"])], "U"))),
  pair("fold2", dynType),
  pair("fold3", dynType),
  pair("fold4", dynType),
  pair("index", bigLamType(["T"], arrty([appty("List", ["T"]), "Number"], "T"))),

  # NOTE(dbp 2013-11-21): I don't know where this is defined (not in sets.rkt in racket-ffi)
  pair("sets", dynType),
  pair("set", bigLamType(["T"], arrty([appty("List", ["T"])], appty("Set", ["T"])))),
  pair("tree-set", bigLamType(["T"], arrty([appty("List", ["T"])], appty("Set", ["T"])))),
  # NOTE(dbp 2013-11-21): Should list-set and tree set be distinct? Probably...
  pair("list-set", bigLamType(["T"], arrty([appty("List", ["T"])], appty("Set", ["T"])))),
  pair("identical", arrowType([anyType, anyType], nmty("Bool"), moreRecord([]))),
  pair("string-to-list", arrty(["String"], appty("List", ["String"]))),

  pair("array", bigLamType(["T"], arrty([appty("List", ["T"])], appty("Array", ["T"])))),
  pair("array-of", bigLamType(["T"], arrty([nmty("T"), nmty("Number")], appty("Array", ["T"])))),
  pair("build-array", bigLamType(["T"], arrty([arrty([nmty("Number")], nmty("T")), nmty("Number")], appty("Array", ["T"])))),
  pair("array-length", bigLamType(["T"], arrty([appty("Array", ["T"])], nmty("Number")))),
  pair("array-get", bigLamType(["T"], arrty([appty("Array", ["T"]), nmty("Number")], nmty("T")))),
  pair("array-set", bigLamType(["T"], arrty([appty("Array", ["T"]), nmty("Number"), nmty("T")], appty("Array", ["T"])))),
  pair("array-to-list", bigLamType(["T"], arrty([appty("Array", ["T"])], appty("List", ["T"])))),

  pair("raise", arrowType([anyType], dynType, moreRecord([]))),
  pair("Racket", dynType),
  pair("Any", arrty([anyType], "Bool")),
  pair("List", arrty([anyType], "Bool")),
  pair("String", arrty([anyType], "Bool")),
  pair("Function", arrty([anyType], "Bool")),
  pair("Bool", arrty([anyType], "Bool")),
  pair("Number", arrty([anyType], "Bool")),
  pair("Nothing", arrty([anyType], "Bool")),
  pair("Mutable", arrty([anyType], "Bool")),
  pair("Placeholder", arrty([anyType], "Bool")),
  pair("Opaque", arrty([anyType], "Bool")),
  pair("Array", arrty([anyType], "Bool")),
  pair("is-bool", arrty([anyType], "Bool")),
  pair("is-boolean", arrty([anyType], "Bool")),
  pair("is-function", arrty([anyType], "Bool")),
  pair("is-method", arrty([anyType], "Bool")),
  pair("is-number", arrty([anyType], "Bool")),
  pair("is-object", arrty([anyType], "Bool")),
  pair("is-string", arrty([anyType], "Bool")),
  pair("is-nothing", arrty([anyType], "Bool")),
  pair("is-mutable", arrty([anyType], "Bool")),
  pair("is-placeholder", arrty([anyType], "Bool")),
  pair("is-array", arrty([anyType], "Bool")),
  pair("brander", arrty([],
      anonType(normalRecord([
            pair("brand", bigLamType(["T"], arrty(["T"], "T"))),
            pair("check", arrty([anyType], "Bool"))
          ])))),
  pair("check-brand", bigLamType(["T"], arrty([arrty(["T"], "Bool"), "T", nmty("String")], "T"))),
  # TODO(dbp 2013-11-21): figure out types for these mk-* functions.
  pair("mk-mutable", dynType),
  pair("mk-simple-mutable", dynType),
  pair("mk-placeholder", arrty([anyType], "Bool")),
  pair("is-nothing", arrty([anyType], "Bool")),
  pair("gensym", arrty(["String"], "String")),
  pair("pi", nmty("Number")),
  pair("prim-has-field", arrty([anyType, "String"], "Bool")),
  pair("prim-keys", arrty([anyType], appty("List", ["String"]))),
  pair("prim-num-keys", arrty([anyType], "Number"))
]

fun tc-main(p, s):
  stx = s^A.parse(p, { ["check"]: false})
  # NOTE(dbp 2013-11-03): This is sort of crummy. Need to get bindings first, for use
  # with inferring functions, but then will do this again when we start type checking...
  bindings = eval(get-bindings(stx.with-types.block), [], [], [], default-datatypes, default-env, default-type-env)
  iifs = eval(is-inferred-functions(stx.pre-desugar.block), [], [], [], bindings.b + default-datatypes, bindings.a + default-env, default-type-env)
  run(infer(stx.with-types.block)^bind(fun(ast):
        tc(ast)
      end), [], [], iifs, default-datatypes, default-env, default-type-env)
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
  eval(tc-branches([return(dynType), return(anyType)]), [], [], [], [], [], default-type-env)
    is branchCompatible(anyType)
  eval(tc-branches([return(dynType), return(anyType),return(nmty("Bool"))]), [], [], [], [], [], default-type-env)
    is branchIncompatible([anyType, nmty("Bool")])
  eval(tc-branches([return(dynType), return(bigLamType(["T"], appty("Option", ["T"]))),
        return(appty("Option", ["Bool"])), return(appty("Option", ["String"]))]), [], [], [], [], [], default-type-env)
    is branchIncompatible([appty("Option", ["Bool"]), appty("Option", ["String"])])
  eval(tc-branches([return(dynType), return(bigLamType(["T"], appty("Option", ["T"]))),
        return(bigLamType(["U"], appty("Option", ["U"]))), return(appty("Option", ["String"]))]), [], [], [], [], [], default-type-env)
    is branchCompatible(appty("Option", ["String"]))

end


################################################################################
# Local type inference.                                                        #
################################################################################
data Constraint:
  | conEq(t1 :: ConTerm, t2 :: ConTerm)
end

fun fmterm(t :: ConTerm) -> String:
  doc: "This function is useful for debugging and displaying unification errors."
  cases(ConTerm) t:
    | conExp(e) =>
      er = torepr(e)
      "exp(" + torepr(e.l.line) + "," + torepr(e.l.column) + "," + er.substring(0, er.index-of("(")) + ")"
    | conVar(id) => "var " + id
    | conPH(name) => "ph " + name
    | conInst(con, args) => "inst " + fmterm(con) + "<" + args.map(fmterm).join-str(",") + ">"
    | conDyn => "Dyn*"
    | conName(name) => name
    | conArrow(args, ret) =>
      "(" + args.map(fmterm).join-str(", ") + " -> " + fmterm(ret) + ")"
    | conMethod(self, args, ret) =>
      "(method " + fmterm(self) + ", " + args.map(fmterm).join-str(", ") + " -> " + fmterm(ret) + ")"
    | conAnon(record) =>
      "{" + record.map(fun(p): p.a + ": " + fmterm(p.b) end).join-str(", ") + "}"
    | conApp(name, args) =>
      fmterm(name) + "<" + args.map(fmterm).join-str(", ") + ">"
    | conBigLam(params, term) =>
      "[" + params.join-str(",") + "]" + fmterm(term)
  end
end

fun fmcon(c :: Constraint) -> String:
  cases(Constraint) c:
    | conEq(t1, t2) =>
      fmterm(t1) + " = " + fmterm(t2) + "\n"
  end
end

data ConTerm:
  | conExp(e :: A.Expr)
  | conVar(id :: String)
  | conPH(name :: String)
  | conInst(con :: ConTerm, args :: List<ConTerm>)
  | conDyn # NOTE(dbp 2013-12-18): This is just a placeholder; in unification
           # anything with conDyn on either side is just thrown out. It allows
           # the type -> conterm function to be total, and to work with functions
           # that are missing annotations.
  | conName(name :: String)
  | conArrow(args :: List<ConTerm>, ret :: ConTerm)
  | conMethod(self :: ConTerm, args :: List<ConTerm>, ret :: ConTerm)
  | conAnon(record :: List<Pair<String, ConTerm>>)
  | conApp(name :: ConTerm, args :: List<ConTerm>)
  | conBigLam(params :: List<String>, term :: ConTerm)
end

fun tycon(t :: Type) -> ConTerm:
  cases(Type) t:
    | dynType => conDyn
    | anyType => conName("Any")
    | nameType(name) => conName(name)
    | anonType(record) =>
      conAnon(record.fields.map(fun(p): pair(p.a, tycon(p.b)) end))
    | arrowType(args, ret, _) => conArrow(args.map(tycon), tycon(ret))
    | methodType(self, args, ret, _) =>
      conMethod(tycon(self), args.map(tycon), tycon(ret))
    | appType(name, args) => conApp(conName(name), args.map(tycon))
    | bigLamType(params, type) => conBigLam(params, tycon(type))
  end
end

data UnifyError:
  | unifyError(t1 :: ConTerm, l1 :: Loc, t2 :: ConTerm, l2 :: Loc)
end

fun add-placeholders(expr1 :: A.Expr, skip :: Bool) -> TCST<Pair<List<String>, A.Expr>>:
  doc: "Skip causes the placeholders not to be added to the outermost expression.
  This prevents double instantiation."
  cases(A.Expr) expr1:
    | s_instantiate(l, e, params) =>
      add-placeholders(e, true)^bind(fun(_e):
          return(pair(_e.a, A.s_instantiate(l, _e.b, params)))
        end)
    | s_id(l, id) =>
      if skip:
        return(pair([], expr1))
      else:
        get-env()^bind(fun(env):
            cases(Option<Type>) map-get(env, id):
              | none => # unbound id, will be caught later
                return(pair([], expr1))
              | some(t) =>
                if is-bigLamType(t):
                  ps = t.params.map(fun(_): gensym("p") end)
                  return(pair(ps, A.s_instantiate(l, A.s_id(l, id), ps.map(A.a_name(l, _)))))
                else:
                  return(pair([], expr1))
                end
            end
          end)
      end
    | s_bracket(l, obj, field) =>
      # NOTE(dbp 2013-12-06): Type checking here to get something to see if we need
      # to instantiate. I'm not sure if this is right, but some form of it needs to happen,
      # as the most common instantiation is going to be list.["empty"] and friends.
      # It is possible better interleaving can make this work (to infer obj before needing
      # to add placeholders).
      add-placeholders(obj, false)^bind(fun(_obj):
          tc-standalone(expr1)^bind(fun(exprty):
              if is-bigLamType(exprty):
                if skip:
                  return(pair(_obj.a, A.s_bracket(l, _obj.b, field)))
                else:
                  ps = exprty.params.map(fun(_): gensym("p") end)
                  return(pair(ps + _obj.a,
                      A.s_instantiate(l, A.s_bracket(l, _obj.b, field), ps.map(A.a_name(l, _)))))
                end
              else:
                return(pair(_obj.a, A.s_bracket(l, _obj.b, field)))
              end
            end)
        end)
    | s_colon_bracket(l, obj, field) =>
      add-placeholders(obj, false)^bind(fun(_obj):
          tc-standalone(expr1)^bind(fun(exprty):
              if is-bigLamType(exprty):
                if skip:
                  return(pair(_obj.a, A.s_colon_bracket(l, _obj.b, field)))
                else:
                  ps = exprty.params.map(fun(_): gensym("p") end)
                  return(pair(ps + _obj.a,
                      A.s_instantiate(l, A.s_colon_bracket(l, _obj.b, field), ps.map(A.a_name(l, _)))))
                end
              else:
                return(pair(obj.a, A.s_colon_bracket(l, _obj.b, field)))
              end
            end)
        end)
    | s_block(l, exprs) =>
      sequence(exprs.map(add-placeholders(_,false)))^bind(fun(_exprs):
          ps = unzip2(_exprs)
          return(pair(ps.a^concat(), A.s_block(l, ps.b)))
        end)
    | s_user_block(l, expr2) =>
      add-placeholders(expr2, false)^bind(fun(p):
          return(pair(p.a, A.s_user_block(p.b)))
        end)
    | s_var(l, r, val) =>
      add-placeholders(val, false)^bind(fun(_val):
          return(pair(_val.a, A.s_var(l, r, _val.b)))
        end)
    | s_let(l, r, val) =>
      add-placeholders(val, false)^bind(fun(_val):
          return(pair(_val.a, A.s_let(l, r, _val.b)))
        end)
    | s_assign(l, n, val) =>
      add-placeholders(val, false)^bind(fun(_val):
          return(pair(_val.a, A.s_assign(l, n, _val.b)))
        end)
    | s_if_else(l, branches, elsebranch) =>
      add-placeholders(elsebranch, false)^bind(fun(_eb):
          sequence(branches.map(fun(b):
                add-placeholders(b.test, false)^bind(fun(_t):
                    add-placeholders(b.body, false)^bind(fun(_b):
                        return(pair(_t.a + _b.a, A.s_if_branch(b.l, _t.b, _b.b)))
                      end)
                  end)
              end))^bind(fun(_branches):
              rezipped = unzip2(_branches)
              return(pair(rezipped.a^concat() + _eb.a, A.s_if_else(l, rezipped.b, _eb.b)))
            end)
        end)
    | s_try(l, body, id, _except) =>
      add-placeholders(body, false)^bind(fun(_body):
          add-placeholders(_except, false)^bind(fun(_exc):
              return(pair(_body.a + _exc.a, A.s_try(l, _body.b, id, _exc.b)))
            end)
        end)
      # NOTE(dbp 2013-12-06): Not going inside functions, as this process will be
      # repeated for each function body.
    | s_lam(l, ps, _args, ann, doc, body, ck) =>  return(pair([], expr1))
    | s_method(l, args, ann, doc, body, ck) => return(pair([], expr1))
    | s_extend(l, super, fields) =>
      add-placeholders(super, false)^bind(fun(_super):
          sequence(fields.map(fun(f):
                add-placeholders(f.value, false)^bind(fun(_v):
                    return(pair(_v.a, A.s_data_field(f.l, f.name, _v.b)))
                  end)
              end))^bind(fun(_fields):
              rezipped = unzip2(_fields)
              return(pair(_super.a + rezipped.a^concat(), A.s_extend(l, _super.b, rezipped.b)))
            end)
        end)
    | s_update(l, super, fields) =>
      add-placeholders(super, false)^bind(fun(_super):
          sequence(fields.map(fun(f):
                add-placeholders(f.value, false)^bind(fun(_v):
                    return(pair(_v.a, A.s_data_field(f.l, f.name, _v.b)))
                  end)
              end))^bind(fun(_fields):
              rezipped = unzip2(_fields)
              return(pair(_super.a + rezipped.a^concat(), A.s_update(l, _super.b, rezipped.b)))
            end)
        end)
    | s_obj(l, fields) =>
      sequence(fields.map(fun(f):
            add-placeholders(f.value, false)^bind(fun(_v):
                return(pair(_v.a, A.s_data_field(f.l, f.name, _v.b)))
              end)
          end))^bind(fun(_fields):
          rezipped = unzip2(_fields)
          return(pair(rezipped.a^concat(), A.s_obj(l, rezipped.b)))
        end)
    | s_app(l, fn, args) =>
      add-placeholders(fn, false)^bind(fun(_fn):
          sequence(args.map(add-placeholders(_, false)))^bind(fun(_args):
              rezipped = unzip2(_args)
              return(pair(_fn.a + rezipped.a^concat(), A.s_app(l, _fn.b, rezipped.b)))
            end)
        end)
    | s_num(l, num) => return(pair([], expr1))
    | s_bool(l, bool) => return(pair([], expr1))
    | s_str(l, str) => return(pair([], expr1))
    | s_get_bang(l, obj, str) =>
      add-placeholders(obj, false)^bind(fun(_obj):
          return(pair(_obj.a, A.s_get_bang(l, _obj.b, str)))
        end)
    | s_datatype(l, name, params, variants, ck) =>
      # NOTE(dbp 2013-12-06): Not going inside constructtors, as this process will be
      # repeated for each.
      add-placeholders(ck, false)^bind(fun(_ck):
          return(pair(_ck.a, A.s_datatype(l, name, params, variants, _ck.b)))
        end)
    | s_cases(l, type, val, branches) =>
      add-placeholders(val, false)^bind(fun(_val):
          sequence(branches.map(fun(b):
                add-placeholders(b.body, false)^bind(fun(bb):
                    return(pair(bb.a, A.s_cases_branch(b.l, b.name, b.args, bb.b)))
                  end)
              end))^bind(fun(_branches):
              rzp = unzip2(_branches)
              return(pair(_val.a + rzp.a^concat(), A.s_cases(l, type, _val.b, rzp.b)))
            end)
        end)
    | s_cases_else(l, type, val, branches, _else) =>
      add-placeholders(val, false)^bind(fun(_val):
          add-placeholders(_else, false)^bind(fun(_els):
              sequence(branches.map(fun(b):
                    add-placeholders(b.body, false)^bind(fun(bb):
                        return(pair(bb.a, A.s_cases_branch(b.l, b.name, b.args, bb)))
                      end)
                  end))^bind(fun(_branches):
                  rzp = unzip2(_branches)
                  return(pair(_val.a + _els.a + rzp.a^concat(),
                      A.s_cases_else(l, type, _val.b, rzp.b, _els.b)))
                end)
            end)
        end)
    | s_list(l, elts) =>
      sequence(elts.map(add-placeholders(_, false)))^bind(fun(_elts):
          elts-unz = unzip2(_elts)
          return(pair(elts-unz.a^concat(), A.s_list(l, elts-unz.b)))
        end)
    | else => raise("add-placeholders: no case matched for: " + torepr(expr1))
  end
where:
  eval-default(add-placeholders(A.s_num(dummy-loc, 1), false)) is pair([], A.s_num(dummy-loc, 1))
  empty-app = eval-default(add-placeholders(A.s_app(dummy-loc, A.s_id(dummy-loc, "empty"), []), false))
  empty-app.a.length() is 1
  empty-app.b satisfies A.is-s_app
  empty-app.b._fun satisfies A.is-s_instantiate
end

fun get-constraints(expr1 :: A.Expr, placeholders :: List<String>) -> TCST<List<Constraint>>:
  gc = get-constraints(_, placeholders)
  cases(A.Expr) expr1:
    | s_block(l, exprs) =>
      sequence(exprs.map(gc))^bind(fun(r): return(concat(r)) end)
    | s_user_block(l, expr2) => gc(expr2)
    | s_var(l, r, val) =>
      get-type(r.ann)^bind(fun(ty):
          gc(val)^bind(fun(cs):
              return(cs + (if is-dynType(ty): [] else: [conEq(conVar(r.id), tycon(ty))] end) +
                [conEq(conVar(r.id), conExp(val))])
            end)
        end)
    | s_let(l, r, val) =>
      get-type(r.ann)^bind(fun(ty):
          gc(val)^bind(fun(cs):
              return(cs + (if is-dynType(ty): [] else: [conEq(conVar(r.id), tycon(ty))] end) + [conEq(conExp(val), conVar(r.id))])
            end)
        end)
    | s_assign(l, n, val) =>
      gc(val)^bind(fun(cs):
          return(cs + [conEq(conVar(n), conExp(val))])
        end)
    | s_if_else(l, branches, elsebranch) =>
      gc(elsebranch)^bind(fun(eb):
          bodies = branches.map(_.body)
          tests = branches.map(_.test)
          sequence(branches.map(fun(b): sequence([gc(b.test),gc(b.body)])^bind(fun(xs): return(concat(xs)) end) end))^bind(fun(bs):
              return(eb + bs^concat() + tests.map(fun(b): conEq(conExp(b), conName("Bool")) end) +
                (for fold(cs from [], b from zip2(link(elsebranch, bodies).map(some), bodies.map(some) + [none])):
                    cases(Option) b.b:
                      | none => cs
                      | some(exp2) => conEq(conExp(b.a.value), conExp(exp2))^link(cs)
                    end
                  end))
            end)
        end)
    | s_try(l, body, id, _except) =>
      gc(body)^bind(fun(b):
          gc(_except)^bind(fun(e):
              return(b + e)
            end)
        end)
    | s_lam(l, ps, _args, ann, doc, body, ck) => return([])
    | s_method(l, args, ann, doc, body, ck) => return([])
    | s_extend(l, super, fields) =>
      gc(super)^bind(fun(s):
          sequence(fields.map(gc))^bind(fun(fs):
              return(s + fs^concat())
            end)
        end)
    | s_update(l, super, fields) =>
      gc(super)^bind(fun(s):
          sequence(fields.map(gc))^bind(fun(fs):
              return(s + fs^concat())
            end)
        end)
    | s_obj(l, fields) =>
      sequence(fields.map(gc))^bind(fun(fs):
          return(fs^concat())
        end)
    | s_app(l, fn, args) =>
      gc(fn)^bind(fun(f):
          sequence(args.map(gc))^bind(fun(acs):
              return(f + acs^concat() + [
                  conEq(conExp(fn), conArrow(args.map(conExp), conExp(expr1)))
                ])
            end)
        end)
    | s_instantiate(l, e, ps) =>
      # NOTE(dbp 2013-12-18): We have said that we cannot pass
      # around foralls as values. This is sort of false (as list has a
      # value in it called link that is certainly a forall), but
      # assuming these are only done for modules and for in scope let
      # bindings then we should have a type for what we are
      # instantiating, and we are NOT trying to solve for it. So we
      # look the type up and eliminate it right now. We could do this with
      # a few cases and NOT use tc (identifiers, brackets), which is probably
      # "the right thing to do".
      tc-standalone(e)^bind(fun(ety):
          fresh-ps = ps.map(fun(_): gensym("p") end)
          fun ty-or-ph(t) -> ConTerm:
            if is-nameType(t) and placeholders.member(t.name):
              conPH(t.name)
            else:
              tycon(t)
            end
          end
          bind-params(placeholders,
            sequence(ps.map(get-type)))^bind(fun(_ps):
              return(
                [ conEq(conExp(expr1), conInst(tycon(ety), _ps.map(ty-or-ph)))
                ])
            end)
        end)
    | s_id(l, id) =>
      get-env()^bind(fun(env):
          cases(Option<Type>) map-get(env, id):
            | none => # unbound id, will cause error later, we don't have to try.
              return([])
            | some(t) =>
              return([conEq(conExp(expr1), conVar(id)), conEq(conVar(id), tycon(t))])
          end
        end)
    | s_num(l, num) => return([conEq(conExp(expr1), conName("Number"))])
    | s_bool(l, bool) => return([conEq(conExp(expr1), conName("Bool"))])
    | s_str(l, str) => return([conEq(conExp(expr1), conName("String"))])
    | s_get_bang(l, obj, str) => gc(obj)
    | s_bracket(l, obj, field) =>
      gc(obj)^bind(fun(ocs):
          return(ocs + [conEq(conExp(obj), conAnon([pair(field.s, conExp(expr1))]))])
        end)
    | s_colon_bracket(l, obj, field) => gc(obj)
    | s_datatype(l, name, params, variants, ck) => return([])
    | s_cases(l, type, val, branches) =>
      get-type(type)^bind(fun(t):
          gc(val)^bind(fun(v):
              sequence(branches.map(fun(b):
                    gc(b.body)
                  end))^bind(fun(bs):
                  return(v + (if is-dynType(t): [] else: [conEq(conExp(val), tycon(t))] end) + bs^concat() + (if branches.length() == 0:
                        []
                      else:
                        for fold(cs from [], b from zip2(branches.map(some), branches.rest.map(some) + [none])):
                          cases(Option) b.b:
                            | none => cs
                            | some(exp2) => link(conEq(conExp(b.a.value.body), conExp(exp2.body)), cs)
                          end
                        end
                      end))
                end)
            end)
        end)
    | s_cases_else(l, type, val, branches, _else) =>
      get-type(type)^bind(fun(t):
          gc(val)^bind(fun(v):
              gc(_else)^bind(fun(e):
                  sequence(branches.map(fun(b):
                        gc(b.body)
                      end))^bind(fun(bs):
                      bodies = branches.map(_.body)
                      return(v + (if is-dynType(t): [] else: [conEq(conExp(val), tycon(t))] end) + bs^concat() +
                        (for fold(cs from [], b from zip2(link(_else, bodies).map(some), bodies.map(some) + [none])):
                            cases(Option) b.b:
                              | none => cs
                              | some(exp2) => link(conEq(conExp(b.a.value), conExp(exp2)), cs)
                            end
                          end))
                    end)
                end)
            end)
        end)
    | s_list(l, elts) =>
      t = gensym("t")
      sequence(elts.map(gc))^bind(fun(elt-cons):
          return([conEq(conExp(expr1), conApp(conName("List"), [conVar(t)]))] +
            elts.map(fun(e): conEq(conExp(e), conVar(t)) end) + elt-cons^concat())
        end)
    | else => raise("get-constraints: no case matched for: " + torepr(expr1))
  end
where:
  n = A.s_num(dummy-loc, 10)
  l = A.s_let(dummy-loc, A.s_bind(dummy-loc, "x", A.a_blank), n)
  eval-default(get-constraints(l, []))
  is [conEq(conExp(n), conName("Number")), conEq(conExp(n), conVar("x"))]
end
fun replace-term(t1 :: ConTerm, t2 :: ConTerm, cs :: List<Pair<ConTerm, ConTerm>>) -> List<Pair<ConTerm, ConTerm>>:
  fun rt(ta :: ConTerm, tb :: ConTerm, td :: ConTerm) -> ConTerm:
    r = rt(ta, tb, _)
    if ta == td:
      tb
    else:
      cases(ConTerm) td:
        | conArrow(args, ret) =>
          conArrow(args.map(r), r(ret))
        | conMethod(self, args, ret) =>
          conMethod(r(self), args.map(r), r(ret))
        | conAnon(record) =>
          conAnon(record.map(fun(p): pair(p.a, r(p.b)) end))
        | conApp(name, args) =>
          conApp(r(name), args.map(r))
        | conInst(con, args) =>
          conInst(r(con), args.map(r))
        | conBigLam(params, term) =>
          conBigLam(params, r(term))
        | else => td
      end
    end
  end
  cases(List<Constraint>) cs:
    | empty => empty
    | link(c, rest) =>
      link(pair(c.a, rt(t1, t2, c.b)),
        replace-term(t1, t2, rest))
  end
end
fun subst-add(t1 :: ConTerm, t2 :: ConTerm, subst :: List<Pair<ConTerm, ConTerm>>) -> List<Pair<ConTerm, ConTerm>>:
  cases(Option<ConTerm>) map-get(subst, t2):
    | none =>
      link(pair(t1, t2), replace-term(t1, t2, subst))
    | some(t3) =>
      link(pair(t1, t3), replace-term(t1, t3, subst))
  end
end
fun unify(constraints :: List<Constraint>, subst :: List<Pair<ConTerm, ConTerm>>) -> TCST<List<Pair<ConTerm, ConTerm>>>:
  fun is-var-type(t :: ConTerm) -> Bool:
    is-conVar(t) or is-conExp(t) or is-conPH(t) or is-conInst(t)
  end
  cases(List<Constraint>) constraints:
    | empty => return(subst)
    | link(c, cs) =>
      t1 = c.t1
      t2 = c.t2
      if is-conDyn(t1) or is-conDyn(t2):
        unify(cs, subst)
      else:
        cases(ConTerm) t1:
          | conVar(id) =>
            cases(Option<ConTerm>) map-get(subst, t1):
              | some(b) => unify(link(conEq(b, t2), cs), subst)
              | none => unify(cs, subst-add(t1, t2, subst))
            end
          | conExp(e) =>
            cases(Option<ConTerm>) map-get(subst, t1):
              | some(b) => unify(link(conEq(b, t2), cs), subst)
              | none => unify(cs, subst-add(t1, t2, subst))
            end
          | conPH(name) =>
            cases(Option<ConTerm>) map-get(subst, t1):
              | some(b) => unify(link(conEq(b, t2), cs), subst)
              | none => unify(cs, subst-add(t1, t2, subst))
            end
          | conInst(con, args) =>
            if is-conInst(t2) and (args.length() == t2.args.length()):
              unify(conEq(con, t2.con)^link(map2(conEq, args, t2.args) + cs), subst)
            else if is-conBigLam(con) and (args.length() == con.params.length()):
              new-term = for fold(term from con.term, s from zip2(con.params, args)):
                # TODO(dbp 2013-12-18): Should write a better replace-term helper.
                replace-term(conName(s.a), s.b, [pair(term,term)]).first.b
              end
              unify(conEq(new-term, t2)^link(cs), subst)
            else if is-var-type(t2):
              unify(conEq(t2, t1)^link(cs), subst)
            else:
              # FIXME(dbp 2013-12-11): actual location info.
              return(unifyError(t1, dummy-loc, t2, dummy-loc))
            end
          | conName(name1) =>
            fun err():
              # FIXME(dbp 2013-12-11): actual location info.
              return(unifyError(t1, dummy-loc, t2, dummy-loc))
            end
            if is-conName(t2) and (t2.name == name1):
              unify(cs, subst)
            else if is-var-type(t2):
              unify(conEq(t2, t1)^link(cs), subst)
            else if is-conAnon(t2):
              # NOTE(dbp 2013-12-18): See if there something in the type env
              get-type-env()^bind(fun(tyenv):
                  cases(TypeBinding) map-get(tyenv, nameType(name1)):
                    | none => err()
                    | some(bnd) =>
                      try:
                        if is-anonType(bnd.type):
                          new-cs = t2.record.map(fun(p):
                              cases(Option<Type>) map-get(bnd.type.record, p.a):
                                | none => raise(none)
                                | some(t) =>
                                  ct = tycon(t)
                                  if is-conMethod(ct):
                                    [conEq(t1, ct.self), conEq(p.b, conArrow(ct.args, ct.ret))]
                                  else:
                                    [conEq(p.b, ct)]
                                  end
                              end
                            end)^concat()
                          unify(new-cs + cs, subst)
                        else:
                          err()
                        end
                      except(e):
                        if is-none(e):
                          err()
                        else:
                          raise(e)
                        end
                      end
                  end
                end)
            else:
              err()
            end
          | conArrow(args, ret) =>
            if is-conArrow(t2) and (args.length() == t2.args.length()):
              unify(map2(conEq, args, t2.args) + [conEq(ret, t2.ret)] + cs, subst)
            else:
              if is-var-type(t2):
                unify(conEq(t2, t1)^link(cs), subst)
              else:
                # FIXME(dbp 2013-12-11): actual location info.
                return(unifyError(t1, dummy-loc, t2, dummy-loc))
              end
            end
          | conMethod(self, args, ret) =>
            if is-conMethod(t2) and (args.length() == t2.args.length()):
              unify(map2(conEq, args, t2.args) +
                [conEq(ret, t2.ret), conEq(self, t2.self)] + cs, subst)
            else:
              if is-var-type(t2):
                unify(conEq(t2, t1)^link(cs), subst)
              else:
                # FIXME(dbp 2013-12-11): actual location info.
                return(unifyError(t1, dummy-loc, t2, dummy-loc))
              end
            end
          | conAnon(record) =>
            # INVARIANT: right record should be width subtype of left record.
            if is-conAnon(t2) and (record.length() >= t2.record.length()):
              keys1 = record.map(_.a)
              keys2 = t2.record.map(_.a)
              if list.all(fun(k): keys1.member(k) end, keys2):
                unify(keys2.map(fun(k):
                      conEq(map-get(record, k).value, map-get(t2.record, k).value)
                    end) + cs, subst)
              else:
                # FIXME(dbp 2013-12-11): actual location info.
                return(unifyError(t1, dummy-loc, t2, dummy-loc))
              end
            else:
              if is-var-type(t2):
                unify(conEq(t2, t1)^link(cs), subst)
              else:
                # FIXME(dbp 2013-12-11): actual location info.
                return(unifyError(t1, dummy-loc, t2, dummy-loc))
              end
            end
          | conApp(name, args) =>
            fun err():
              # FIXME(dbp 2013-12-11): actual location info.
              return(unifyError(t1, dummy-loc, t2, dummy-loc))
            end
            if is-conApp(t2) and (args.length() == t2.args.length()):
              unify(link(conEq(name, t2.name), map2(conEq, args, t2.args)) + cs,
                subst)
            else if is-var-type(t2):
              unify(conEq(t2, t1)^link(cs), subst)
            else if is-conName(name) and is-conAnon(t2):
              # NOTE(dbp 2013-12-18): See if there something in the type env
              get-type-env()^bind(fun(tyenv):
                  cases(Option<TypeBinding>) map-get(tyenv, nameType(name.name)):
                    | none => err()
                    | some(bnd1) =>
                      if is-bigLamType(bnd1.type) and is-appType(bnd1.type.type):
                        cases(Option<TypeBinding>) map-get(tyenv, bnd1.type):
                          | none => err()
                          | some(bnd) =>
                            try:
                              if is-anonType(bnd.type):
                                new-cs = t2.record.map(fun(p):
                                    cases(Option<Type>) map-get(bnd.type.record.fields, p.a):
                                      | none => raise(none)
                                      | some(t) =>
                                        ct = tycon(t)
                                        fresh-ps = bnd1.type.params.map(fun(_): gensym("p") end)
                                        if is-conMethod(ct):
                                          [conEq(t1, conInst(conBigLam(bnd1.type.params, ct.self), fresh-ps.map(conVar))), conEq(p.b, conInst(conBigLam(bnd1.type.params, conArrow(ct.args, ct.ret)), fresh-ps.map(conVar)))]
                                        else:
                                          [conEq(p.b, conInst(conBigLam(bnd1.type.params, ct), fresh-ps.map(conVar)))]
                                        end
                                    end
                                  end)^concat()
                                unify(new-cs + cs, subst)
                              else:
                                err()
                              end
                            except(e):
                              if is-none(e):
                                err()
                              else:
                                raise(e)
                              end
                            end
                        end
                      else:
                        err()
                      end
                  end
                end)
            else:
              # FIXME(dbp 2013-12-11): actual location info.
              return(unifyError(t1, dummy-loc, t2, dummy-loc))
            end
          | conBigLam(params, term) =>
            if is-conBigLam(t2) and (params.length() == t2.params.length()):
              # FIXME(dbp 2013-12-11): How do you unify bigLams?
              unify(cs, subst)
            else:
              if is-var-type(t2):
                unify(conEq(t2, t1)^link(cs), subst)
              else:
                # FIXME(dbp 2013-12-11): actual location info.
                return(unifyError(t1, dummy-loc, t2, dummy-loc))
              end
            end
        end
      end
  end
where:
  n = A.s_num(dummy-loc, 10)
  l = A.s_let(dummy-loc, A.s_bind(dummy-loc, "x", A.a_blank), n)
  eval-default(unify([conEq(conExp(n), conName("Number")), conEq(conVar("x"), conExp(n))], [])) is [pair(conVar("x"), conName("Number")), pair(conExp(n), conName("Number"))]
end
fun replace-placeholders(
    subst :: List<Pair<ConTerm, ConTerm>>,
    placeholders :: List<String>,
    expr1 :: A.Expr) -> A.Expr:
  fun ct-to-ty(c :: ConTerm) -> Option<Type>:
    cases(ConTerm) c:
      | conDyn => some(dynType)
      | conName(name) => some(nmty(name))
      | conArrow(args, ret) =>
        all-options(args.map(ct-to-ty))^chain(fun(_args):
            ct-to-ty(ret)^chain(fun(_ret):
                some(arrty(_args, _ret))
              end)
          end)
      | conMethod(self, args, ret) =>
        all-options(args.map(ct-to-ty))^chain(fun(_args):
            ct-to-ty(ret)^chain(fun(_ret):
                ct-to-ty(self)^chain(fun(_self):
                    some(methodType(_self, _args, _ret))
                  end)
              end)
          end)
      | conAnon(record) =>
        cases(Option) (for fold(flds from some([]), p from record):
                cases(Option) flds:
                  | none => none
                  | some(flds1) =>
                    cases(Option) ct-to-ty(p.b):
                      | none => none
                      | some(t) => some(pair(p.a, t)^link(flds1))
                    end
                end
              end):
          | none => none
          | some(flds) =>
            some(anonType(normalRecord(flds.reverse())))
        end
      | conApp(name, args) =>
        cases(ConTerm) name:
          | conName(n) => all-options(args.map(ct-to-ty))^chain(fun(_args): some(appty(n, _args)) end)
          | else => none
        end
      | conInst(con, args) =>
        cases(ConTerm) con:
          | conBigLam(params, term) =>
            if args.length() <> params.length():
              none
            else:
              for fold(t from term, p from zip2(args, params)):
                replace-term(conVar(p.b), p.a, [t]).first
              end
            end
          | else => none
        end
      | conBigLam(params, term) =>
        ct-to-ty(term)^chain(fun(_term): some(bigLamType(params, _term)) end)
      | else => none
    end
  end
  fun replace-placeholder(ph :: String, t :: Type, expr2 :: A.Expr) -> A.Expr:
    r = replace-placeholder(ph, t, _)
    rb = fun(b): if A.is-a_name(b.ann) and (b.ann.id == ph):
        A.s_bind(b.l, b.id, unget-type(t))
      else:
        b
      end
    end
    cases(A.Expr) expr2:
      | s_instantiate(l, e, params) =>
        A.s_instantiate(l, r(e), params.map(fun(a): if A.is-a_name(a) and (a.id == ph): unget-type(t, a.l) else: a end end))
      | s_id(l, id) => expr2
      | s_bracket(l, obj, field) =>
        A.s_bracket(l, r(obj), field)
      | s_colon_bracket(l, obj, field) =>
        A.s_colon_bracket(l, r(obj), field)
      | s_block(l, exprs) =>
        A.s_block(l, exprs.map(r))
      | s_user_block(l, expr3) =>
        A.s_user_block(l, r(expr3))
      | s_var(l, nm, val) =>
        A.s_var(l, rb(nm), r(val))
      | s_let(l, nm, val) =>
        A.s_let(l, rb(nm), r(val))
      | s_assign(l, n, val) =>
        A.s_assign(l, rb(r), r(val))
      | s_if_else(l, branches, elsebranch) =>
        A.s_if_else(l, branches.map(fun(b):
              A.s_if_branch(b.l, r(b.test), r(b.body))
            end), r(elsebranch))
      | s_try(l, body, id, _except) =>
        A.s_try(l, r(body), id, r(_except))
      | s_lam(l, ps, _args, ann, doc, body, ck) =>
        expr2
      | s_method(l, args, ann, doc, body, ck) =>
        expr2
      | s_extend(l, super, fields) =>
        A.s_extend(l, r(super), fields.map(fun(f): A.s_data_field(f.l, f.name, r(f.value)) end))
      | s_update(l, super, fields) =>
        A.s_update(l, r(super), fields.map(fun(f): A.s_data_field(f.l, f.name, r(f.value)) end))
      | s_obj(l, fields) =>
        A.s_obj(l, fields.map(fun(f): A.s_data_field(f.l, f.name, r(f.value)) end))
      | s_app(l, fn, args) =>
        A.s_app(l, r(fn), args.map(r))
      | s_num(l, num) => expr2
      | s_bool(l, bool) => expr2
      | s_str(l, str) => expr2
      | s_get_bang(l, obj, str) => A.s_get_bang(l, r(obj), str)
      | s_datatype(l, name, params, variants, ck) => expr2
      | s_cases(l, type, val, branches) =>
        A.s_cases(l, type, r(val), branches.map(fun(b): A.s_cases_branch(b.l, b.name, b.args, r(b.body)) end))
      | s_cases_else(l, type, val, branches, _else) =>
        A.s_cases_else(l, type, r(val), branches.map(fun(b): A.s_cases_branch(b.l, b.name, b.args, r(b.body)) end), r(_else))
      | s_list(l, elts) =>
        A.s_list(l, elts.map(r))
      | else => raise("replace-placeholder: no case matched for: " + torepr(expr2))
    end
  end
  for fold(ast from expr1, p from placeholders):
    cases(Option<ConTerm>) map-get(subst, conPH(p)):
      | none =>
        # NOTE(dbp 2013-12-18): Should this be a failure / abort? It
        # means we weren't able to solve.
        replace-placeholder(p, dynType, ast)
      | some(con) =>
        cases(Option<Type>) ct-to-ty(con):
          | none =>
            # NOTE(dbp 2013-12-18): Should this be a failure / abort? It
            # means we weren't able to solve.
            replace-placeholder(p, dynType, ast)
          | some(ty) =>
            replace-placeholder(p, ty, ast)
        end
    end
  end
end


fun infer(expr :: A.Expr) -> TCST<A.Expr>:
  # NOTE(dbp 2013-12-18): We need bindings for s_instantiate - because we need to eliminate the instantiation when
  # we constraint solve (so we need to know the type of what we are instantiating, which is in the env).
  get-bindings(expr)^bind(fun(bindings):
      add-bindings(bindings.a,
        add-datatypes(bindings.b,
          add-placeholders(expr, false)^bind(fun(phres):
              if phres.a.length() == 0:
                infer-find(expr)
              else:
                get-constraints(phres.b, phres.a)
                ^bind(fun(constraints):
                    unify(constraints, [])^bind(fun(subst):
                        if is-unifyError(subst):
                          add-error(expr.l, msg(errUnification(subst.t1, subst.l1, subst.t2, subst.l2)))
                          ^bind(fun(_):
                              dummy-subst = phres.a.map(fun(p): pair(conPH(p), conDyn) end)
                              replaced = replace-placeholders(dummy-subst, phres.a, phres.b)
                              infer-find(replaced)
                            end)
                        else:
                          replaced = replace-placeholders(subst, phres.a, phres.b)
                          infer-find(replaced)
                        end
                      end)
                  end)
              end
            end)
          )
        )
    end)
where:
  fun gen-loc(l :: Number, c :: Number) -> Loc:
    loc("gen-file", l, c)
  end
  # NOTE(dbp 2013-12-19): These tests _suck_ in terms of verbosity,
  # but I'd need to write a ast comparison that ignores locations
  # (like jpolitz has in racket), because the locations of the
  # instantiate nodes will be different than when you write them in
  # syntax.

  # x :: List<Number> = empty ===> x :: List<Number> = empty<Number>
  eval-default(infer(A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_id(gen-loc(1,0), "empty")))) is A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_instantiate(gen-loc(1,0), A.s_id(gen-loc(1,0), "empty"), [A.a_name(gen-loc(1,0), "Number")]))

  # x :: List<Number> = link(10, empty<Number>) ===> x :: List<Number> = link<Number>(10, empty<Number>)
  eval-default(infer(A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_app(gen-loc(1,0), A.s_id(gen-loc(1,1), "link"), [A.s_num(gen-loc(1,2), 10), A.s_instantiate(gen-loc(1,3), A.s_id(gen-loc(1,3), "empty"), [A.a_name(gen-loc(1,3), "Number")])])))) is
  A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_app(gen-loc(1,0), A.s_instantiate(gen-loc(1,1), A.s_id(gen-loc(1,1), "link"), [A.a_name(gen-loc(1,1), "Number")]), [A.s_num(gen-loc(1,2), 10), A.s_instantiate(gen-loc(1,3), A.s_id(gen-loc(1,3), "empty"), [A.a_name(gen-loc(1,3), "Number")])]))

  # x :: List<Number> = link(10, empty) ===> x :: List<Number> = link<Number>(10, empty<Number>)
  eval-default(infer(A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_app(gen-loc(1,0), A.s_id(gen-loc(1,1), "link"), [A.s_num(gen-loc(1,2), 10), A.s_id(gen-loc(1,3), "empty")])))) is
  A.s_let(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_name(gen-loc(0,4), "Number")])), A.s_app(gen-loc(1,0), A.s_instantiate(gen-loc(1,1), A.s_id(gen-loc(1,1), "link"), [A.a_name(gen-loc(1,1), "Number")]), [A.s_num(gen-loc(1,2), 10), A.s_instantiate(gen-loc(1,3), A.s_id(gen-loc(1,3), "empty"), [A.a_name(gen-loc(1,3), "Number")])]))

  # link(10, empty) ===> link<Number>(10, empty<Number>)
  eval-default(infer(A.s_app(gen-loc(1,0), A.s_id(gen-loc(1,1), "link"), [A.s_num(gen-loc(1,2), 10), A.s_id(gen-loc(1,3), "empty")]))) is
  A.s_app(gen-loc(1,0), A.s_instantiate(gen-loc(1,1), A.s_id(gen-loc(1,1), "link"), [A.a_name(gen-loc(1,1), "Number")]), [A.s_num(gen-loc(1,2), 10), A.s_instantiate(gen-loc(1,3), A.s_id(gen-loc(1,3), "empty"), [A.a_name(gen-loc(1,3), "Number")])])

  # var x :: List<{in :: Number, out :: Number}> = empty ===> var x :: List<{in :: Number, out :: Number}> = empty<{in :: Number, out :: Number}>
  eval-default(infer(A.s_var(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_record(gen-loc(0,4), [A.a_field(gen-loc(0,5), "in", A.a_name(gen-loc(0,6), "Number")), A.a_field(gen-loc(0,5), "out", A.a_name(gen-loc(0,6), "Number"))])])), A.s_id(gen-loc(1,0), "empty")))) is
  A.s_var(gen-loc(0,0), A.s_bind(gen-loc(0,1), "x", A.a_app(gen-loc(0,2), A.a_name(gen-loc(0,3), "List"), [A.a_record(gen-loc(0,4), [A.a_field(gen-loc(0,5), "in", A.a_name(gen-loc(0,6), "Number")), A.a_field(gen-loc(0,5), "out", A.a_name(gen-loc(0,6), "Number"))])])),  A.s_instantiate(gen-loc(1,0), A.s_id(gen-loc(1,0), "empty"), [A.a_record(gen-loc(1,0), [A.a_field(gen-loc(1,0), "in", A.a_name(gen-loc(1,0), "Number")), A.a_field(gen-loc(1,0), "out", A.a_name(gen-loc(1,0), "Number"))])]))


  # fun foo(): x :: List<Number> = empty end ===> fun foo(): x :: List<Number> = empty<Number> end
  eval-default(infer(A.s_lam(gen-loc(0,0), [], [], A.a_blank, "", A.s_let(gen-loc(1,0), A.s_bind(gen-loc(1,1), "x", A.a_app(gen-loc(1,2), A.a_name(gen-loc(1,3), "List"), [A.a_name(gen-loc(1,4), "Number")])), A.s_id(gen-loc(2,0), "empty")), A.s_block(gen-loc(3,0), [])))) is
  A.s_lam(gen-loc(0,0), [], [], A.a_blank, "", A.s_let(gen-loc(1,0), A.s_bind(gen-loc(1,1), "x", A.a_app(gen-loc(1,2), A.a_name(gen-loc(1,3), "List"), [A.a_name(gen-loc(1,4), "Number")])), A.s_instantiate(gen-loc(2,0), A.s_id(gen-loc(2,0), "empty"), [A.a_name(gen-loc(2,0), "Number")])), A.s_block(gen-loc(3,0), []))

end

fun infer-find(expr :: A.Expr) -> TCST<A.Expr>:
  get-type-bindings(expr)^bind(fun(newtypes):
      add-types(newtypes,
        get-bindings(expr)^bind(fun(bindings):
            add-bindings(bindings.a,
              add-datatypes(bindings.b,
                cases(A.Expr) expr:
                  | s_block(l, exprs) =>
                    sequence(exprs.map(infer-find))^bind(fun(_exprs):
                        return(A.s_block(l, _exprs))
                      end)
                  | s_user_block(l, expr1) =>
                    infer-find(expr1)^bind(fun(e): return(A.s_user_block(l, e)) end)
                  | s_instantiate(l, expr1, params) =>
                    infer-find(expr1)^bind(fun(e): return(A.s_instantiate(l, e, params)) end)
                  | s_var(l, r, val) =>
                    infer-find(val)^bind(fun(e): return(A.s_var(l, r, e)) end)
                  | s_let(l, r, val) =>
                    infer-find(val)^bind(fun(e): return(A.s_let(l, r, e)) end)
                  | s_assign(l, n, val) =>
                    infer-find(val)^bind(fun(e): return(A.s_assign(l, n, e)) end)
                  | s_if_else(l, branches, elsebranch) =>
                    sequence(branches.map(fun(b):
                          infer-find(b.test)^bind(fun(bt):
                              infer-find(b.body)^bind(fun(bb):
                                  return(A.s_if_branch(b.l, bt, bb))
                                end)
                            end)
                        end))^bind(fun(branches_):
                        infer-find(elsebranch)^bind(fun(elsebranch_):
                            return(A.s_if_else(l, branches_, elsebranch_))
                          end)
                      end)
                  | s_try(l, body, id, _except) =>
                    infer-find(body)^bind(fun(body_):
                        infer-find(_except)^bind(fun(except_):
                            return(A.s_try(l, body_, id, except_))
                          end)
                      end)
                  | s_lam(l, ps, _args, ann, doc, body, ck) =>
                    bind-params(ps,
                      sequence(_args.map(fun(b): get-type(b.ann)^bind(fun(t):
                                return(pair(b.id, t))
                            end) end))^
                      bind(fun(args):
                          add-bindings(args,
                            infer(body)^bind(fun(body_):
                                infer(ck)^bind(fun(ck_):
                                    return(A.s_lam(l, ps, _args, ann, doc, body_, ck_))
                                  end)
                              end)
                            )
                        end)
                      )
                  | s_method(l, _args, ann, doc, body, ck) =>
                    sequence(_args.map(fun(b): get-type(b.ann)^bind(fun(t):
                              return(pair(b.id, t))
                          end) end))^
                    bind(fun(args):
                        add-bindings(args,
                          infer(body)^bind(fun(body_):
                              infer-find(ck)^bind(fun(ck_):
                                  return(A.s_method(l, _args, ann, doc, body_, ck_))
                                end)
                            end)
                          )
                      end)
                  | s_extend(l, super, fields) =>
                    infer-find(super)^bind(fun(super_):
                        sequence(fields.map(fun(f):
                              infer-find(f.value)^bind(fun(fv):
                                  return(A.s_data_field(f.l, f.name, fv))
                                end)
                            end))^bind(fun(fields_):
                            return(A.s_extend(l, super_, fields_))
                          end)
                      end)
                  | s_update(l, super, fields) =>
                    infer-find(super)^bind(fun(super_):
                        sequence(fields.map(fun(f):
                              infer-find(f.value)^bind(fun(fv):
                                  return(A.s_data_field(f.l, f.name, fv))
                                end)
                            end))^bind(fun(fields_):
                            return(A.s_update(l, super_, fields_))
                          end)
                      end)
                  | s_obj(l, fields) =>
                    sequence(fields.map(fun(f):
                          infer-find(f.value)^bind(fun(fv):
                              return(A.s_data_field(f.l, f.name, fv))
                            end)
                        end))^bind(fun(fields_):
                        return(A.s_obj(l, fields_))
                      end)
                  | s_app(l, fn, args) =>
                    infer-find(fn)^bind(fun(_fn):
                        sequence(args.map(infer-find))^bind(fun(args_):
                            return(A.s_app(l, _fn, args_))
                          end)
                      end)
                  | s_id(l, id) => return(expr)
                  | s_num(l, num) => return(expr)
                  | s_bool(l, bool) => return(expr)
                  | s_str(l, str) => return(expr)
                  | s_get_bang(l, obj, str) =>
                    infer-find(obj)^bind(fun(obj_): return(A.s_get_bang(l, obj_, str)) end)
                  | s_bracket(l, obj, field) =>
                    infer-find(obj)^bind(fun(obj_):
                        infer-find(field)^bind(fun(field_):
                            return(A.s_bracket(l, obj_, field_))
                          end)
                      end)
                  | s_colon_bracket(l, obj, field) =>
                    infer-find(obj)^bind(fun(obj_):
                        infer-find(field)^bind(fun(field_):
                            return(A.s_bracket(l, obj_, field_))
                          end)
                      end)
                  | s_datatype(l, name, params, variants, ck) =>
                    infer-find(ck)^bind(fun(check_):
                        sequence(variants.map(fun(v):
                              cases(A.Variant) v:
                                | s_datatype_variant(l1, name1, members, constructor) =>
                                  sequence(members.map(fun(m):
                                        get-type(m.bind.ann)^bind(fun(t):
                                            return(pair(m.bind.id, t))
                                          end)
                                      end))^bind(fun(membertys):
                                      add-bindings([pair(constructor.self, anonType(normalRecord(membertys)))],
                                        infer(constructor.body)^bind(fun(cb):
                                            return(A.s_datatype_variant(l1, name1, members,
                                                A.s_datatype_constructor(
                                                  constructor.l,
                                                  constructor.self,
                                                  cb
                                                  )))
                                          end))
                                    end)
                                | s_datatype_singleton_variant(l1, name1, constructor) =>
                                  add-bindings([pair(constructor.self, anonType(normalRecord([])))],
                                    infer(constructor.body)^bind(fun(cb):
                                        return(A.s_datatype_singleton_variant(l1, name1,
                                            A.s_datatype_constructor(
                                              constructor.l,
                                              constructor.self,
                                              cb
                                              )))
                                      end))
                              end
                            end))^bind(fun(variants_):
                            return(A.s_datatype(l, name, params, variants_, check_))
                          end)
                      end)
                  | s_cases(l, type, val, branches) =>
                    infer-find(val)^bind(fun(val_):
                        sequence(branches.map(fun(b):
                              infer-find(b.body)^bind(fun(bb):
                                  return(A.s_cases_branch(b.l, b.name, b.args, bb))
                                end)
                            end))^bind(fun(branches_):
                            return(A.s_cases(l, type, val_, branches_))
                          end)
                      end)
                  | s_cases_else(l, type, val, branches, _else) =>
                    infer-find(_else)^bind(fun(else_):
                        infer-find(val)^bind(fun(val_):
                            sequence(branches.map(fun(b):
                                  infer-find(b.body)^bind(fun(bb):
                                      return(A.s_cases_branch(b.l, b.name, b.args, bb))
                                    end)
                                end))^bind(fun(branches_):
                                return(A.s_cases_else(l, type, val_, branches_, else_))
                              end)
                          end)
                      end)
                  | s_list(l, values) =>
                    sequence(values.map(infer-find))^bind(fun(values_): return(A.s_list(l, values_)) end)
                  | else => raise("infer-find: no case matched for: " + torepr(expr))
                end
                )
              )
          end)
        )
    end)
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
                      else if (ty <> bindty) and (bindty <> dynType):
                        add-warning(l, wmsg(warnBindingDyn(name.id, bindty)))^seq(return(bindty))
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
  fun tc-args(args_ :: List<A.Expr>, arg-types :: List<Type>, ret-type :: Type) -> TCST<Type>:
    sequence(args_.map(tc))^bind(fun(arg-vals):
        (for foldm(base from pair(1, ret-type), ap from zip2(arg-types, arg-vals)):
            subtype(l, ap.b, ap.a)^bind(fun(res):
                if not res:
                  add-error(l,
                    msg(errArgumentBadType(base.a, fmty(ap.a), fmty(ap.b))))
                  ^seq(return(pair(base.a + 1, dynType)))
                else:
                  return(pair(base.a + 1, base.b))
                end
              end)
          end)^bind(fun(p): return(p.b) end)
      end)
  end
  tc(fn)^bind(fun(fn-ty):
      cases(Type) fn-ty:
        | arrowType(arg-types, ret-type, rec-type) =>
          if args.length() <> arg-types.length():
            add-error(l,
              msg(errArityMismatch(arg-types.length(), args.length())))^seq(
              return(dynType))
          else:
            tc-args(args, arg-types, ret-type)
          end
        | bigLamType(params, ty1) =>
          cases(Type) ty1:
            | arrowType(arg-types, ret-type, rec-type) =>
              if args.length() <> arg-types.length():
                add-error(l,
                  msg(errArityMismatch(arg-types.length(), args.length())))^seq(
                  return(dynType))
              else:
                add-error(l, msg(errApplyUninstantiatedFunction(fn-ty)))^seq(return(dynType))
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
            if tydyneq(nmty("Bool"), ty):
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
                        cases(Option) map-get(type-env, typebind.type):
                          | none => raise("tc-bracket: Found a parametric type for " + name + " in env, but not the record of methods, which shouldn't be able to happen.")
                          | some(methods) =>
                            if is-typeNominal(methods) and is-anonType(methods.type):
                              record-lookup(methods.type.record)^bind(fun(mty):
                                  return(
                                    for fold(ty from mty, p from zip2(args, params)):
                                      replace(nmty(p.b), p.a, ty)
                                    end)
                                end)
                            else:
                              raise("tc-bracket: Found a parametric type for " + name + " in env, but the record of methods wasn't there, which shouldn't be able to happen.")
                            end
                        end
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
  get-type(_type)^bind(
    fun(type):
      when is-bigLamType(type):
        raise("tc-cases: encountered uninstantiated type in type position, which means there is a bug in infer.")
      end
      get-datatypes()^bind(fun(datatypes):
          fun data-name(t :: Type) -> Option<String>:
            cases(Type) t:
              | nameType(n) => some(n)
              | appType(n, _) => some(n)
              | else => none
            end
          end
          fun data-def-get(dd :: DataDef, name :: String) -> Option<List<Type>>:
            cs = dd.constructors
            cs.find(fun(c): c.name == name end)^chain(fun(c): some(c.args) end)
          end
          cases(Option) data-name(type)^chain(fun(name): map-get(datatypes, name) end):
            | none =>
              add-error(l, msg(errCasesInvalidType(type)))^seq(return(dynType))
            | some(data-def) =>
              if (data-def.params == []) and is-appType(type):
                add-error(l, msg(errCasesMalformedType(nmty(data-def.name), type)))
                ^seq(return(dynType))
              else if (data-def.params <> []) and ((not is-appType(type)) or (data-def.params.length() <> type.args.length())):
                  add-error(l, msg(errCasesMalformedType(appty(data-def.name, data-def.params), type)))
                ^seq(return(dynType))
              else:
                tc(val)^bind(
                  fun(val-ty):
                    if not tydyneq(type, val-ty):
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
                                  cases(Option) data-def-get(data-def, branch.name):
                                    | none => add-error(branch.l,
                                        msg(errCasesBranchInvalidVariant(fmty(type), branch.name, "Unknown"))
                                        )^seq(return(dynType))
                                    | some(args) =>
                                      if args.length() <> branch.args.length():
                                        add-error(branch.l,
                                          msg(errCasesPatternNumberFields(branch.name, args.length(), branch.args.length()))
                                          )^seq(return(dynType))
                                      else:
                                        argtys = if data-def.params <> []:
                                          for fold(base from args, p from zip2(data-def.params, type.args)):
                                            base.map(replace(nmty(p.a), p.b, _))
                                          end
                                        else:
                                          args
                                        end
                                        add-bindings(for map2(bnd from branch.args,
                                              argty from argtys):
                                            pair(bnd.id, argty)
                                          end,
                                          tc(branch.body))
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
              end
          end
        end)
    end)
end


################################################################################
# Main typechecking function.                                                  #
################################################################################

fun tc-standalone(expr :: A.Expr) -> TCST<Type>:
  doc: "A little helper get types when we don't want to record errors (as they will
  be seen again later)."
  get-errors()^bind(fun(errs):
      get-warnings()^bind(fun(warns):
          tc(expr)^bind(fun(ty):
              put-errors(errs)
              ^seq(put-warnings(warns))
              ^seq(return(ty))
            end)
        end)
    end)
end

fun tc(ast :: A.Expr) -> TCST<Type>:
  get-type-bindings(ast)^bind(fun(newtypes):
      add-types(newtypes,
        get-bindings(ast)^bind(fun(bindings):
            add-bindings(bindings.a,
              add-datatypes(bindings.b,
                cases(A.Expr) ast:
                  | s_block(l, stmts) =>
                    sequence(stmts.map(tc))^bind(
                      fun(tys):
                        return(if tys == []: nmty("Nothing") else: tys.last() end)
                      end)
                  | s_user_block(l, block) => tc(block)
                    # NOTE(dbp 2013-11-10): As of now, the type system does not know about mutation,
                    # so vars look like lets.
                  | s_hint_expr(l, hs, e) => tc(e)
                  | s_instantiate(l, expr, _params) =>
                    tc(expr)^bind(fun(exprty):
                        sequence(_params.map(get-type))^bind(fun(params):
                            cases(Type) exprty:
                              | bigLamType(ps, type) =>
                                if ps.length() <> params.length():
                                  if is-arrowType(type):
                                    add-error(l, msg(errParamArityMismatch(ps.length(), params.length())))
                                    ^seq(return(dynType))
                                  else:
                                    add-error(l,
                                      msg(errInstantiateArityMismatch(type, ps.length(), params.length())))
                                    ^seq(return(dynType))
                                  end
                                else:
                                  inst-type = for fold(base from type, rp from zip2(ps, params)):
                                    replace(nmty(rp.a), rp.b, base)
                                  end
                                  return(inst-type)
                                end
                              | else =>
                                add-error(l, msg(errInstantiateNonParametric(exprty, params)))
                                ^seq(return(dynType))
                            end
                          end)
                      end)
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
                  | s_app(l, fn, args) =>
                    tc-app(l, fn, args)
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
                  | s_datatype(l, name, params, variants, ck) =>
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
                    infer(values.foldr(fun(v, rst): A.s_app(l, A.s_id(l, "link"), [v, rst]) end, A.s_id(l, "empty")))^bind(tc)
                  | else => raise("tc: no case matched for: " + torepr(ast))
                end
                )
              )
          end
          )
        )
    end
    )
where:
  fun tc-src(src):
    stx = A.parse(src,"anonymous-file", { ["check"]: false}).with-types
    eval(infer(stx.block)^bind(tc), [], [], [], default-datatypes, default-env, default-type-env)
  end
  fun tc-stx(stx):
    eval(infer(stx)^bind(tc), [], [], [], default-datatypes, default-env, default-type-env)
  end
  tc-src("1") is nmty("Number")
  tc-src("[1]") is appty("List", ["Number"])
  tc-src("[1,2,3]") is appty("List", ["Number"])
  tc-stx(A.s_list(dummy-loc, [A.s_num(dummy-loc, 1)])) is appty("List", ["Number"])
  tc-stx(A.s_list(dummy-loc, [A.s_num(dummy-loc, 1), A.s_num(dummy-loc, 2)])) is appty("List", ["Number"])
end
