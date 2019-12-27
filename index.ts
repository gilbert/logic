import debug from 'debug'

const log = debug('logic')
const log_unify = debug('logic:unify')

type Rule = {
  type: 'rule',
  head: Atom
  body: Atom[]
}
type Atom = {
  type: 'atom'
  predSym: string
  terms: Term[]
}

type Var = { type: 'var', name: string }
type Sym = { type: 'sym', name: string }
type Term = Var | Sym

type Program = Rule[]
type KnowledgeBase = Atom[]
/**
 * Applying a substitution to an atom or variable potentially makes it *ground*.
 * That is, the substitution replaces it with a constant.
 */
type Substitution = (readonly [Var,Sym])[]

const Rule = (head: Atom, body: Atom[]=[]): Rule => ({ type: 'rule', head, body })
const Atom = (predSym: string, terms: Term[]=[]): Atom => ({ type: 'atom', predSym, terms })
const Var = (name: string): Var => ({ type: 'var', name })
const Sym = (name: string): Sym => ({ type: 'sym', name })

const emptySubstitution: Substitution = []

function lookup(var_: Var, sub: Substitution): Term | null {
  const s = sub.find(s => s[0].name === var_.name)
  return s ? s[1] : null
}

function substitute(atom: Atom, sub: Substitution): Atom {
  return {
    ...atom,
    terms: atom.terms.map(term =>
      term.type === 'sym' ? term :  // If symbol, no need to substitute.
      lookup(term, sub) || term     // If var is not found, just leave it alone.
    )
  }
}

function unify(a: Atom, b: Atom): Substitution | null {
  log_unify('Unifying atoms', a, 'and', b)
  if (a.predSym !== b.predSym) {
    log_unify('Predicates not equal.')
    return null
  }
  const result = _unify(zip(a.terms, b.terms))
  log_unify('Unify result:', result)
  return result
}
function _unify(terms: [Term, Term][]): Substitution | null {
  if (terms.length === 0) return emptySubstitution

  const [[a,b], ...rest] = terms
  log_unify('Unifying terms', a, 'and', 'b')
  if (a.type === 'sym' && b.type === 'sym') {
    log_unify('sym')
    //
    // In Datalog, unification is based on sym.name AND arity (# of terms).
    // This rudimentary implementation does not check arity.
    //
    return a.name === b.name ? _unify(rest) : null
  }
  if (a.type === 'var' && b.type === 'sym') {
    log_unify('var & sym')
    const incompleteSub = _unify(rest)
    if (!incompleteSub) {
      log_unify('abort')
      return null
    }

    const varSub = lookup(a, incompleteSub)
    if (varSub && varSub.name !== b.name) {
      log_unify('repeated var', b.name, varSub.name)
      //
      // Do not unify unless both names are the same.
      // Handles cases such as p(X,X) ~? p(a,b) by failing them.
      //
      return null
    }

    log_unify('unified term!')

    return [[a,b] as const].concat(incompleteSub)
  }
  //
  // Unification only occurs between a body atom and a fact.
  // Since facts cannot have variables, we shouldn't ever get to this point.
  //
  throw new Error(`The second atom must be grounded`)
}

function evalAtom(kb: KnowledgeBase, atom: Atom, substitutions: Substitution[]): Substitution[] {
  log('evalAtom', kb.length, printAtom(atom))
  return substitutions.map(sub => {
    const downToEarthAtom = substitute(atom, sub)

    const matches = kb.map(atom =>
      unify(downToEarthAtom, atom)
    )
    .filter(notNullish)

    return matches.map(extension =>
      sub.concat(extension)
    )
  }).reduce(concat, [])
}

function walk(kb: KnowledgeBase, atoms: Atom[]): Substitution[] {
  log('walk')
  return atoms.reduceRight((sub, atom) => evalAtom(kb, atom, sub), [emptySubstitution])
}

function evalRule(kb: KnowledgeBase, rule: Rule): KnowledgeBase {
  log('evalRule', kb.length, printRule(rule))
  const subs = walk(kb, rule.body)
  log('evalRule -> subs', subs.map(sub => sub.map(printSub)))
  const newFacts = subs.map(sub => substitute(rule.head, sub))
  log('newFacts', printKB(newFacts))
  return newFacts
}

function immediateConsequence(rules: Program, kb: KnowledgeBase): KnowledgeBase {
  log('immediateConsequence', rules.length, kb.length)
  // nub . (kb <>) . concatMap (evalRule kb) $ rules
  const atoms = kb.concat(
    rules.map(r => evalRule(kb, r)).reduce(concat, [])
  )
  // log('immediateConsequence -> new kb', inspect(atoms))
  return dedupe(atoms)
}

function solve(rules: Program): KnowledgeBase {
  if (!rules.every(isRangeRestricted)) {
    throw new Error('The input program is not range-restricted.')
  }
  // console.log("Solving", inspect(rules))
  log("Solving", rules.length)
  let currentKB = [] as KnowledgeBase
  //
  // Datalog is guaranteed to terminate, but
  // that's assuming we implement it correctly.
  //
  let safety = 10000
  while (safety-- > 0) {
    const nextKB = immediateConsequence(rules, currentKB)
    log("Next", printKB(nextKB))
    if (basic_eq(nextKB, currentKB)) {
      break
    }
    currentKB = nextKB
  }
  return currentKB
}

function isRangeRestricted(rule: Rule): boolean {
  const headVars = _vars(rule.head)
  const bodyVars = rule.body.map(_vars).reduce(concat, [])
  return headVars.every(hv => !!bodyVars.find(bv => basic_eq(hv, bv)))
}
function _vars(atom: Atom) {
  return dedupe(
    atom.terms.filter(t => t.type === 'var')
  )
}

//
// Helpers
//
function zip<T>(a: T[], b: T[]): [T,T][] {
  // Haskell's `zip` semantics is to use shortest length
  const upperBound = Math.min(a.length, b.length)
  const results: [T,T][] = []
  for (let i=0; i < upperBound; i++) {
    results.push([a[i], b[i]])
  }
  return results
}

function notNullish<T> (x: T | null | undefined): x is T {
  return x !== null && x !== undefined
}

function concat<T>(a: T[], b:T[]) {
  return a.concat(b)
}

function isObject(x: unknown) {
  return ({}).toString.call(x).match(/\[object (\w+)\]/)![1] === 'Object'
}

function basic_eq<T>(a: T, b: T): boolean {
  if (Array.isArray(a)) {
    return Array.isArray(b) && Object.keys(a).every(i => basic_eq(a[+i], b[+i]))
  }
  if (isObject(a)) {
    if (!isObject(b)) return false
    const a_keys = Object.keys(a)
    return a_keys.length === Object.keys(b).length && a_keys.every(k => basic_eq((a as any)[k], (b as any)[k]))
  }
  return a === b
}

function dedupe<T>(items: T[]): T[] {
  if (items.length === 0) return items

  const [x, ...xs] = items
  const without_x = xs.filter(y => !basic_eq(x,y))
  return [x].concat(dedupe(without_x))
}

function isVarText(text: string) {
  return /^[A-Z_]/.test(text)
}

type MagicProxy = Record<string, (...atoms: any[]) => void>

export function createProgram () {
  let idCounter = 200
  const potentialRules = new Set<Rule | Atom>()

  const proxy: MagicProxy = new Proxy({}, {
    has(_target, name) {
      return typeof name === 'string'
    },
    get(_target, prop) {
      console.log("GET", prop)
      if (prop === Symbol.unscopables) {
        return null
      }
      const termId = idCounter++

      const term = function createAtomOrRule(...args: any[]) {
        let ruleBody: Atom[] | null = null

        const terms: Term[] = args.map((a, i) => {
          if (Array.isArray(a)) {
            if (i !== args.length - 1) {
              throw new Error(`'${String(prop)}' is invalid: A rule's body array must appear as the last argument`)
            }
            a.forEach(bodyAtom => {
              console.log("Body term", bodyAtom)
              if (bodyAtom.type === 'rule') {
                throw new Error(`Rule '${String(prop)}' is invalid: Rules may not have nested rules.`)
              }
              potentialRules.delete(bodyAtom)
              return bodyAtom
            })
            ruleBody = a
            return null
          }
          else if (typeof a === 'function') {
            return isVarText(a.text) ? Var(a.text) : Sym(a.text)
          }
          else if (typeof a === 'string') {
            // TODO: Actually support string data
            return Sym(a)
          }
          else {
            throw new Error(`Unsupported term: '${JSON.stringify(a)}'`)
          }
        })
        .filter(notNullish)

        if (ruleBody) {
          const rule = Rule(
            Atom(String(prop), terms),
            ruleBody
          )
          potentialRules.add(rule)
          return rule
        }
        else {
          const atom = Atom(String(prop), terms)
          potentialRules.add(atom)
          return atom
        }

      }
      term.id = termId
      term.text = prop
      return term
    },
  })

  function getRules () {
    return Array.from(potentialRules, (value) =>
      value.type === 'atom' ? Rule(value) : value
    )
  }

  let queryId = 1

  function query(f: (proxy: MagicProxy) => void) {
    const atoms = [] as Atom[]
    const queryProxy = new Proxy({}, {
      has(_target, name) {
        return typeof name === 'string'
      },
      get(_target, prop) {

        const term = function createAtomOrRule(...args: any[]) {
          const terms = args.map(a => {
            if (Array.isArray(a)) {
              throw new Error(`'${String(prop)}' is invalid: Query atoms may not have bodies.`)
            }
            else if (typeof a === 'function') {
              return isVarText(a.text) ? Var(a.text) : Sym(a.text)
            }
            else if (typeof a === 'string') {
              // TODO: Actually support string data
              return Sym(a)
            }
            else {
              throw new Error(`Unsupported term: '${JSON.stringify(a)}'`)
            }
          })

          const atom = Atom(String(prop), terms)
          atoms.push(atom)
          return atoms
        }
        term.text = prop
        return term
      }
    })

    f(queryProxy)

    const querySym = `query${queryId++}`

    const queryRule = Rule(
      Atom(
        querySym,
        dedupe(atoms.map(a => a.terms.filter(t => t.type === 'var')).reduce(concat, []))
      ),
      atoms
    )

    const program = getRules().concat(queryRule)
    const result = solve(program)

    const queryVarsResult = program.filter(r => r.head.predSym === querySym).map(r => r.head.terms)

    // An array of solutions
    const querySolutions = result.filter(a => a.predSym === querySym).map(a => a.terms)

    if (queryVarsResult.length === 0) {
      throw `The query '${querySym}' does not exist.`
    }
    else if (queryVarsResult.length >= 2) {
      throw `The query '${querySym}' has multiple clauses.`
    }
    const queryVars = queryVarsResult[0]

    // LAST TIME: [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    // LAST TIME: [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    // LAST TIME: [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    // LAST TIME: [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms
    // LAST TIME: [ queryVars ] -> zip queryVars <$> relevantKnowledgeBaseSyms

    // TODO: Make this a generator
    // console.log("RELEVANT", require('util').inspect(querySolutions, { depth: 10 }))

    return querySolutions.map(solution =>
      solution.map((term, i) => [queryVars[i], term] as const)
    )
  }

  return { proxy, getRules, query }
}


function printRule(rule: Rule) {
  let output = printAtom(rule.head)
  if (rule.body.length) {
    output += ` :- ${rule.body.map(printAtom).join(', ')}`
  }
  return output + '.'
}
function printAtom(a: Atom) {
  return `${a.predSym}(${a.terms.map(printTerm).join(',')})`
}
function printTerm(t: Term) {
  switch (t.type) {
    case 'var': return t.name
    case 'sym': return `"${t.name}"`
  }
}
function printSub(s: Substitution[number]) {
  return `${printTerm(s[0])} -> ${printTerm(s[1])}`
}

function printKB(kb: KnowledgeBase) {
  return '\n    ' + kb.map(printAtom).join(',\n    ') + '.'
}

export function printQueryResult(solutions: (readonly [Term,Term])[][]) {
  return solutions.map(solution =>
    solution.map(([var_, val]) =>
      `${printTerm(var_)} = ${printTerm(val)}`
    ).join(', ')
  ).join(';\n')
}
