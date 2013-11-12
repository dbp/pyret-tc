#lang pyret

#! identifier x was defined to have type String, but assigned a value of an incompatible type: Foo

datatype Foo:
| foo with constructor(self): self end
end

x :: String = foo