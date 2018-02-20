import groovy.transform.Field
import org.testng.collections.ListMultiMap

import static groovy.io.FileType.FILES

@Field ListMultiMap<Integer, List> map = ListMultiMap.create()
@Field formula = []
@Field int numberOfVariables = 0
@Field int numberOfClauses = 0
@Field assignment
@Field def mapSizeArray = []
ListMultiMap<Integer, List> mapSize = ListMultiMap.create()
@Field cnfFile
@Field result = []

def loadInputFile() {
    cnfFile = new File(args[0])
    def lines = cnfFile.readLines()
    def numberOfClauses
    for (int iterate = 0; iterate < lines.size(); iterate++) {
        def line = lines[iterate].split(" ")
        if (line[0] != 'c') {
            if (line[0] == 'p') {
                numberOfClauses = Integer.parseInt(line[2])
                numberOfVariables = Integer.parseInt(line[3])
            } else {
                try {
                    def singleClause = []
                    if (Integer.parseInt(line[0]) != 0)
                        singleClause << Integer.parseInt(line[0])
                    if (Integer.parseInt(line[1]) != 0)
                        singleClause << Integer.parseInt(line[1])
                    formula << singleClause
                }
                catch (ArrayIndexOutOfBoundsException e) {}

            }
        }
    }
    assignment = new Integer[numberOfVariables + 1]
    println(formula)
    initializeMap()
    getTheAssignment()
    manipulateMaxIndex()
    println(assignment)
}


def initializeMap() {
    for (List clause : formula) {
        for (int element : clause) {
            if (clause.size() == 1) {
                if (element > 0) {
                    assignment[element] = 1
                } else if (element < 0) {
                    assignment[-1 * element] = -1
                }
            } else {
                map.put(element, clause)
            }
        }
//        println(assignment)
    }

    for (int i = 1; i <= numberOfVariables; i++) {
        def el = map.get(i)
        if (el != null) {
            mapSizeArray[i] = el.size()
        } else {
            mapSizeArray[i] = 0
        }
        el = map.get(i * -1)
        if (el != null) {
            mapSizeArray[i + numberOfVariables] = el.size()
        } else {
            mapSizeArray[i + numberOfVariables] = 0
        }
    }
    def makeTrue = []
    for (int i = 1; i <= numberOfVariables; i++) {
        if (assignment[i] != null)
            if (assignment[i] == 1) {
                makeTrue << i
            } else {
                makeTrue << i
            }
        }
    for (int el : makeTrue) {
        if (el > 0) {
            makeOthersTrue(el, el)
        }
        else
            makeOthersTrue(i, i + numberOfVariables)
    }
    }

//}

int getMaxIndex() {
    def max = 0
    def index = -1
    for (int i = 1; i <= 2 * numberOfVariables; i++) {
        if (max < mapSizeArray[i]) {
            max = mapSizeArray[i]
            index = i
        }
    }
    return index
}

def getZeroIndex() {
//    def max = 0
//    def index = 0
    def zerolist = []
    for (int i = 1; i <= numberOfVariables; i++) {
        if (mapSizeArray[i] == 0) {
            if (assignment[i] == null) {
//                return i
                zerolist << i
            }

        } else if (mapSizeArray[i + numberOfVariables] == 0) {
            if (assignment[Math.abs(i - numberOfVariables)] == null) {
//                return -1 * i
                zerolist << -1 * i
            }
        }
    }
    return zerolist
}

def manipulateMaxIndex() {
    def index = getMaxIndex()
    def sign = null
    def indexToManipulate = 0
    while (index > 0) {
        if (index <= numberOfVariables) {
            indexToManipulate = index
            sign = 1
            mapSizeArray[index] = -1
        } else {
            indexToManipulate = numberOfVariables - index
            sign = -1
            mapSizeArray[index] = -1
        }
        if (assignment[Math.abs(indexToManipulate)] == null) { //yet to be assigned
            assignment[Math.abs(indexToManipulate)] = sign // assigned with truth value
            decreaseCount(indexToManipulate, index)
        } else {
            mapSizeArray[index] = -1
        }
        index = getMaxIndex()
    }
    checkSat()
}

def decreaseCount(int reference, int longIndex) {
//    println(reference)
    mapSizeArray[longIndex] = -1 //zeroing out max count
    def listOfClauses = map.get(reference)
//    println(listOfClauses)

    for (List clauseInList : listOfClauses) {
        def zind = clauseInList[0]
        if (zind > 0)
            mapSizeArray[zind] -= 1
        else {
            zind = (zind * -1) + numberOfVariables
            mapSizeArray[zind] -= 1
        }
        zind = clauseInList[1]
        if (zind > 0)
            mapSizeArray[zind] -= 1
        else {
            zind = (zind * -1) + numberOfVariables
            mapSizeArray[zind] -= 1
        }
    }
}


boolean assignTheAssignment() {
    def clauseFlag = false
    def sat = true
    for (List clause : formula) {
        if (clause == []) {
            return false
        }
        for (int element : clause) {
            if (assignment[Math.abs(element)] == null) {
                assignment[Math.abs(element)] = -1
            }
            if ((assignment[Math.abs(element)] * element) < 0) {
                clauseFlag = false
            } else {
                clauseFlag = true
                break
            }

        }
        if (!clauseFlag) {
            return sat = false
        }

    }
    if (formula == []) {
        return false
    }
    return sat
}

boolean checkSat() {
    def sat = assignTheAssignment()
    if (sat) {
        println("SAT")
        result << args[0] + " " + "SAT " + assignment.toString()
        println(assignment)

    } else {
        println("UNSAT")
        result << args[0] + " " + "UNSAT "
    }
    res = new File("All2CNFResult.txt")
    res << System.getProperty("line.separator").toString() + result

}


def getTheAssignment() {
    def indexToFlip = getZeroIndex()
    for (int flip : indexToFlip) {
        if (flip < 0) {
            int nullIndex = (flip * -1) + numberOfVariables
            mapSizeArray[nullIndex] = -1
            if (assignment[-1 * flip] == null) {
                assignment[Math.abs(flip)] = 1
            }
        } else {
            mapSizeArray[flip] = -1
            if (assignment[flip] == null) {
                assignment[flip] = -1
            }
        }
    }
}

loadInputFile()
//getTheAssignment()
//manipulateMaxIndex()

def makeOthersTrue(int reference, int longIndex) {
    def listOfClauses = map.get(-1 * reference)
    for (List clauseInList : listOfClauses) {
        for (int zind : clauseInList) {
            if (zind != -1 * reference && zind != 0) {
                if (zind > 0) {
//                    println(zind)
                    mapSizeArray[zind] = -1
                    if (assignment[zind] == null)
                    assignment[zind] = 1
//                    makeOthersTrue(zind, zind)
                }
                else if (zind < 0 && zind != -1 *reference) {
                    mapSizeArray[zind * -1 + numberOfVariables] = -1
                    if (assignment[zind * -1] == null )
                        assignment[zind * -1] = -1
//                    makeOthersTrue(zind, -1*zind+numberOfVariables)
                }
            }
        }
    }
}