const fs = require('fs')
const { execSync } = require('child_process')

const Minisat = require('./lib/minisat.js')
const solveString = Minisat.cwrap('solve_string', 'string', ['string', 'number']);

// All of the packages in the repository ordered by their SAT number
const satNumber = [null]

/** Class representing a package in the repository */
class Package {
    /**
     * Create a package
     * @param {String} name The package name
     * @param {String} version The package version
     * @param {Number} size The package size
     * @param {Array} dependencies The package's dependencies
     * @param {Array} conflicts The package's conflicts
     */
    constructor (name, version, size, dependencies = [], conflicts = []) {
        this.name = name
        this.version = this.formatVersion(version)
        this.unformattedVersion = version
        this.size = size
        this.dependencies = []
        this.conflicts = []
        this.dependencyConstraints = this.parseDependencyConstraints(dependencies)
        this.conflictConstraints = []
        conflicts.forEach(item => this.conflictConstraints.push(new Constraint(item)))
        this.satNumber = satNumber.push(this) - 1
    }

    /**
     * Format a version number into x.y.z format
     * e.g. 1 -> 1.0.0
     * @param {String} input The number to be formatted
     * @return {String} The formatted number
     */
    formatVersion (input) {
        if (input === undefined) return undefined
        while (input.length < 5) input = input + '.0'
        return input
    }

    /**
     * Parse an array of dependencies into an array of Constraints
     * @param {Array} dependencyData The dependency data
     * @return {Array} The array of constraints
     */
    parseDependencyConstraints (dependencyData) {
        let constraintArray = []

        dependencyData.forEach(constraintData => {
            Array.isArray(constraintData)
                ? constraintArray.push(this.parseDependencyConstraints(constraintData))
                : constraintArray.push(new Constraint(constraintData))
        })

        return constraintArray
    }

    /**
     * Uses an array of dependency constraints in order to initialise the arrays
     * of dependency and conflict properties
     * @param {JSON} repository The repository in JSON format
     */
    findConstraintOptions (repository) {
        // Initialise dependencies
        this.dependencies = []
        this.dependencyConstraints.forEach(constraintArray => {
            let dependant = [] // rename
            constraintArray.forEach(constraint => {
                (repository.get(constraint.name) || []).forEach(packageItem => {
                    if (constraint.fulfilledBy(packageItem)) dependant.push(packageItem)
                })
            })
            if (dependant.length) this.dependencies.push(dependant)
        })

        // Initialise conflicts
        this.conflicts = [] 
        this.conflictConstraints.forEach(constraint => {
            (repository.get(constraint.name) || []).forEach(packageInRepo => {
                if (constraint.fulfilledBy(packageInRepo)) { this.conflicts.push(packageInRepo) }
            })
        })

        // Rationalise
        this.conflicts.forEach(conflict => {
            this.dependencies.forEach(dependsList => {
                if (dependsList.includes(conflict)) dependsList.splice(dependsList.indexOf(conflict), 1); // Dubious
            })
        })
    }

    /**
     * Formats the package name for printing etc.
     * @return {String} The formatted name e.g. A=3.0.2
     */
    formattedName () {
        return `${this.name}=${this.unformattedVersion}`
    }
}

/** A class to represent a constraint, such as a conflict or a dependency */
class Constraint {
    /**
     * Create a constraint
     * @param {Array} data The constraint data
     */
    constructor (data) {
        const regex = /([.+a-zA-Z0-9-]+)(=|<|>|<=|>=)([0-9.]+)/
        const [, name, constraint, version] = data.match(regex) || [, data]

        this.name = name
        this.constraint = constraint
        this.version = this.formatVersion(version)
        this.unformattedVersion = version
    }

    /**
     * Checks if this constraint is fulfilled by an input package
     * @param {Package} inputPackage The package to check if fulfills this constraint
     * @return {Boolean} Whether the constraint is fulfilled by the input package
     */
    fulfilledBy (inputPackage) {
        if (this.name != inputPackage.name) return false
        if (this.constraint === undefined && this.version === undefined) return true

        const constraintMap = {
            '=': inputPackage.version === this.version,
            '>': inputPackage.version > this.version,
            '<': inputPackage.version < this.version,
            '<=': inputPackage.version <= this.version,
            '>=': inputPackage.version >= this.version
        }

        return constraintMap[this.constraint] || false
    }

    /**
     * Formats the package name for printing etc.
     * @return {String} The formatted name e.g. A=3.0.2
     */
    formatVersion (input) {
        if (input === undefined) return undefined
        while (input.length < 5) input = input + '.0'
        return input
    }
}

/**
 * Parses a repository, an initial state and constraints into
 * A Map representing the repository containing packages and an array
 * for uninstall, install and initial containing packages
 * @param {JSON} repositoryData The repository in JSON form
 * @param {JSON} initialData The initial state in JSON form
 * @param {JSON} constraintsData The constraints in JSON form
 * @return {[Map, Array, Array, Array]} The repository, initial, install and uninstall represntations
 */
const parse = (repositoryData, initialData, constraintsData) => {
    // Parse repository
    let repository = new Map()
    repositoryData.forEach(item => {
        const package = new Package(item.name, item.version, item.size, item.depends, item.conflicts)
        let data = repository.get(package.name) || []
        data.push(package)
        repository.set(package.name, data)
    })
    repository.forEach(package => {
        package.forEach(version => {
            version.findConstraintOptions(repository)
        })
    })

    // Parse initial data
    let initial = []
    initialData.forEach(version => {
        const constraint = new Constraint(version)
        repository.get(constraint.name).some(package => {
            constraint.fulfilledBy(package) ? (initial.push(package), true) : false
        })
    })

    // Parse constraints
    let uninstall = [], install = []
    const uninstallToken = '-'
    constraintsData.forEach(constraintData => {
        const constraint = new Constraint(constraintData.toString().substring(1))
        if (constraintData[0] === uninstallToken) {
            (repository.get(constraint.name) || []).some(package => {
                constraint.fulfilledBy(package) ? (uninstall.push(package), true) : false
            })
        } else install.push(constraint)
    })

    return [repository, initial, install, uninstall]
}

/**
 * Converts a repository, install and uninstall requirements
 * into CNF form to be fed into a SAT solver
 * @param {Map} repository The repository
 * @param {Array} install The packages to install
 * @param {Array} uninstall The packages to uninstall
 * @return {Array} The problem in CNF form, with each item of the array representing a line
 */
const convertToCnf = (repository, install, uninstall) => {
    let output = []
    repository.forEach(package => {
        package.forEach(version => {
            version.conflicts.forEach(conflict => output.push(`${-version.satNumber} ${-conflict.satNumber} 0\n`))
            version.dependencies.forEach(depedency => {
                let subClause = [-version.satNumber]
                depedency.forEach(possible => subClause.push(possible.satNumber))
                output.push(subClause.join(" ") + ' 0\n')
            })
        })
    })

    uninstall.forEach(package => output.push(`${-package.satNumber} 0\n`))

    install.forEach(constraint => {
        let subClause = []
        repository.get(constraint.name).forEach(package => {
            if (constraint.fulfilledBy(package)) subClause.push(package.satNumber)
        })
        output.push(subClause.join(' ') + ' 0\n')
    })

    output.unshift(`p cnf ${satNumber.length - 1} ${output.length}\n`)
    return output
}

/**
 * Runs a SAT solver on a CNF problem in order to create
 * an array of the packages that need to be added and removed
 * @param {Array} cnf The CNF problem
 * @return {[Array, Array]} The packages to be added and removed
 */
const runSolver = (cnf) => {
    const successCode = 'SAT'
    const cnfString = cnf.join('')
    let result = undefined

    fs.writeFileSync('problem.txt', cnfString, 'utf8', () => {})

    try {
        execSync('minisat problem.txt solution.txt', () => {})
    } catch(e) { }

    const data = fs.readFileSync('./solution.txt', 'utf8', () => {})
    // If our minisat has not worked then fall back to the JS transpiled version
    data ? result = data : result = solveString(cnfString, cnfString.length)
        
    if (result.substring(0,3) !== successCode) throw 'Unsatisfiable CNF'

    const satNumbers = result.substring(4).split(' ')
    let addPackages = [], removePackages = []

    satNumbers.forEach(number => {
       const package = satNumber[Math.abs(number)]
       number > 0 ? addPackages.push(package) : removePackages.push(package)
    })

    return [addPackages , removePackages]
}

/**
 * Perform a topological sort on a graph represented by a map of vertices
 * and arcs
 * @param {Map} nodes The map of vertices in the graph
 * @param {Map} count The map of arcs in the graph
 * @return {Array} The sorted vertices
 */
const topological = (nodes, count) => {
    let output = [], toRemove = []

    for (const key of nodes.keys()) if (!count.get(key)) toRemove.push(key)

    for (let i = 0; i < nodes.size; i++) {
        if (!toRemove.length) throw 'Topological sorting error'
        const node = toRemove.pop()
        output.push(node)
        nodes.get(node).forEach(outgoing => {
            const newCount = (count.get(outgoing) || 0) + 1
            count.set(outgoing, newCount)
            if (!count.get(outgoing) && !toRemove.includes(outgoing)) insortLeft(toRemove, outgoing)
        })
    }

    return output
}

/**
 * Convert a list of SAT numbers representing packets into removal commands
 * @param {Array} packetsToRemove An array of SAT numbers to remove
 * @param {Array} initial The initial installation state
 * @return {[Array, Array, Number]} An array containing the installation commands,
 *  the new initial state and the total cost of the removal commands
 */
const createRemoveCommands = (packetsToRemove, initial) => {
    const rationalised = packetsToRemove.filter(item => initial.includes(item))

    let nodes = new Map(), count = new Map()
    rationalised.forEach(item => {
        nodes.set(item.satNumber, [])
        count.set(item.satNumber, 0)
    })

    rationalised.forEach(package => {
        package.dependencies.forEach(dependencyArray => {
            dependencyArray.forEach(depedency => {
                if (packetsToRemove.includes(depedency)) {
					let initialValue = nodes.get(depedency.satNumber) || []
					initialValue.push(package.satNumber)
                    nodes.set(depedency.satNumber, initialValue)

                    let currentCount = count.get(package.satNumber) || 0
                    let newCount = currentCount++
                    count.set(package.satNumber, newCount)
                }
            })
        })
    })

    const removeSatNumbers = topological(nodes, count)//.reverse()
    const commands = removeSatNumbers.map(element => `-${satNumber[element].formattedName()}`)
    const newInitial = initial.filter(item => !packetsToRemove.includes(item))
    const cost = removeSatNumbers.length * 1000000

    return [commands, newInitial, cost]
}

/**
 * Convert a list of SAT numbers representing packets into installation commands
 * @param {Array} packetsToAdd An array of SAT numbers to add
 * @param {Array} initial The initial installation state
 * @return {[Array, Array, Number]} An array containing the installation commands,
 *  the new initial state and the total cost of the install commands
 */
const createAddCommands = (packetsToAdd, initial = []) => {
    const rationalised = packetsToAdd.filter(item => !initial.includes(item))

    let nodes = new Map(), count = new Map()
    rationalised.forEach(item => {
        nodes.set(item.satNumber, [])
        count.set(item.satNumber, 0)
    })

    rationalised.forEach(package => {
        package.dependencies.forEach(dependencyArray => {
            let fulfilled = false
            dependencyArray.some(dependency =>initial.includes(dependency) ? (fulfilled = true, true) : false)
            if (!fulfilled) {
                dependencyArray.some(depedency => {
                    if (rationalised.includes(depedency)) {
                        let current = nodes.get(depedency.satNumber) || []
                        current.push(package.satNumber)
                        nodes.set(depedency.satNumber, current)
                        
                        let currentCount = count.get(package.satNumber) || 0
                        let newCount = currentCount++
                        count.set(package.satNumber, newCount)

                        fulfilled = true
                        return true
                    } else return false
                })
            }
            if (!fulfilled) throw "Cannot Satisfy"
        })
    })

    const addSatNumbers = topological(nodes, count)//.reverse()
    const commands = addSatNumbers.map(element => `+${satNumber[element].formattedName()}`)
    const newInitial = initial.concat(rationalised)
    const cost = addSatNumbers.reduce((a, v) =>  a + satNumber[v].size, 0 )

    return [commands, newInitial, cost]
}

/**
 * Finds all solutions to a problem by running a SAT solver and then returns
 * The commands to perform the lowest cost solution
 * @param {Array} repository The repository
 * @param {Array} initial The initial installation state
 * @param {Array} install The packages to install
 * @param {Array} uninstall The packages to uninstall
 */
const solveCnf = (repository, initial, install, uninstall) => {
    let cnf = convertToCnf(repository, install, uninstall)
    let lowestCost = -1
    let lowestCommands = []

    while (true) {
        try {
            let [addP, removeP] = runSolver(cnf)
            let [removeCommands, newInitial, removeCost] = createRemoveCommands(removeP, initial)
            let [addCommands, _, addCost] = createAddCommands(addP, newInitial)

            // Add this solution as a NOT to the end of the CNF
            let updated = cnf.slice(0)
            let subClause = []

            updated.shift()
            addP.forEach(element => subClause.push(-element.satNumber))
            updated.push(subClause.join(" ") + ' 0\n')
            updated.unshift(`p cnf ${satNumber.length - 1} ${cnf.length}\n`)
            cnf = updated

            // If this solution has the lowest cost so far, update the lowest values
            if ((lowestCost === -1) || ((addCost + removeCost) < lowestCost)) {
                lowestCost = addCost + removeCost
                lowestCommands = removeCommands.concat(addCommands)
            }

        } catch (e) {
            break
        }
    }

    return lowestCommands
}

/**
 * Bisect left an array
 * @param {Array} input 
 * @param {Number} point 
 * @param {Number} low 
 * @param {Number} high 
 */
const bisectLeft = (input, point ,low = 0 ,high = input.length ) => {
    while ( low < high ) {
        const mid = ( low + high ) / 2 | 0
        if ( point > input[mid] ) low = mid + 1
        else high = mid
    }
    return low
}

/**
 * Insort left an array
 * @param {Array} input 
 * @param {Number} point 
 * @param {Number} low 
 * @param {Number} high 
 */
const insortLeft = (input, point, low = 0, high = input.length) => {
	const pos = bisectLeft( input , point , low , high )
	input.splice( pos , 0 , point )
}

const r = require('./' + process.argv[2])
const i = require('./' + process.argv[3])
const c = require('./' + process.argv[4])

// const r = require('../tests/seen-4/repository.json')
// const i = require('../tests/seen-4/initial.json')
// const c = require('../tests/seen-4/constraints.json')

const [repository, initial, install, uninstall] =  parse(r, i, c)

/**
 * If the number of packages is too high then we just search for any solution,
 * instead of the most optimal.
 * 
 * Command generation is chained in setTimeout in order to constantly clear the stack
 * and prevent any memory issues we may run into with large repositories
 */
if(satNumber.length > 50000) {
	let cnf = convertToCnf(repository, install, uninstall)
	let addP, removeP, removeCommands, addCommands, newInitial
	setTimeout(() => { [addP, removeP] = runSolver(cnf) }, 0)
	setTimeout(() => { [removeCommands, newInitial, _] = createRemoveCommands(removeP, initial) }, 0)
	setTimeout(() => { [addCommands, _, _] = createAddCommands(addP, newInitial) }, 0)
	setTimeout(() => {
		const commands = removeCommands.concat(addCommands)
		console.log('%j', commands)
	}, 0)
} else {
	const commands = solveCnf(repository, initial, install, uninstall)
	console.log('%j', commands)
}

//const json = JSON.stringify(commands)
//fs.writeFile('commands.json', json, 'utf8', () => {})
