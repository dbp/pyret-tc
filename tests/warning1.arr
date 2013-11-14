#lang pyret

#~ Function body had Number specified as a return type, but type checker found Dyn

fun f() -> Number:
  builtins.keys({})
end