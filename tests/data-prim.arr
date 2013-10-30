#lang pyret

datatype Foo:
| foo with constructor(self): self end
end

x :: String = foo