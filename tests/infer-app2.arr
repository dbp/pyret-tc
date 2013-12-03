#lang pyret

#! Function with type <T>(T, List<T> -> List<T>) not compatible with arguments Number, List<String>

#~ 'x' had List<Number> specified as type, but type checker found Dyn

x :: List<Number> = list.["link"](1, list.["empty"]<String>)