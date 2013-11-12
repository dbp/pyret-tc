#lang pyret

#! identifier y was defined to have type {foo : Number}, but assigned a value of an incompatible type: {foo : String}

x :: {} = {}
y :: {foo : Number} = x.{foo: "Foo"}