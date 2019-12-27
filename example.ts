import {createProgram, printQueryResult} from './index'

const program = createProgram()

;(({
  adviser,
  academicAncestor,
  X, Y, Z,
}) => {

  adviser('Andrew Rice',     'Mistral Contrastin')
  adviser('Dominic Orchard', 'Mistral Contrastin')
  adviser('Andy Hopper',     'Andrew Rice')
  adviser('Alan Mycroft',    'Dominic Orchard')
  adviser('David Wheeler',   'Andy Hopper')
  adviser('Rod Burstall',    'Alan Mycroft')
  adviser('Robin Milner',    'Alan Mycroft')

  academicAncestor(X, Y, [
    adviser(X,Y)
  ])
  academicAncestor(X, Z, [
    adviser(X,Y),
    academicAncestor(Y,Z)
  ])

})(program.proxy)

const queryResult = program.query(({
  academicAncestor,
  Intermediate,
}) => {
  academicAncestor('Robin Milner', Intermediate)
  academicAncestor(Intermediate, 'Mistral Contrastin')
})

console.log("Query result:")
console.log(printQueryResult(queryResult))
