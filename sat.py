import time 
import sys

#################################################
#Clause represents a disjunction of literals
class Clause:
    def __init__(self):
        self.variables = dict() #Key: string name, Value: bool sign

    def addVariable(self, variable, boolean):
        self.variables[variable] = boolean
    
    def getValue(self, var, value):
        sign = self.variables[var]
        if(sign):
            return value
        else: 
            return not value

    def stringClause(self):
        s = ""
        for var in (self.variables):
            sign = ""
            if(not self.variables[var]):
                sign = "¬"
            s = s + sign + var +" ∨ "
        return s[:-2]

    #True: if at least one var Not assigned or disconjuction True
    #False: if all var assigned and disconjuction False
    def consistent(self, assignments):
        result = False
        for variable in self.variables:
            var_assigned = False
            for assignment in assignments:
                if(variable == assignment[0]):
                    var_assigned = True
                    value = assignment[1]
                    if(not self.variables[variable]): 
                        value = not value
                    result = result or value
            if(not var_assigned): 
                return True
        return result

###################################################
#Represents a conjunction of clauses
class SAT:

    def __init__(self):
        self.clauses = []
        self.unitaryAssignments = []     # list of all Vars in unitary clauses
        self.variablesUnassiged = dict() # unassigned Var : [satisfiable_value, frequency, is_pure]
        self.nb_2b = 0
        self.partialModelSatisfied = True

    def readSATFile(self, file):
        f = open(file, "r")
        lines = f.readlines()

        for line in lines:
            #comments
            if line[0] == 'c':
                pass
            #primary info
            elif line[0] == 'p':
                self.nbVariables = int(line.split()[2])
                self.nbClauses   = int(line.split()[3])
            #end of file
            elif line[0] == '%':
                break
            #content
            elif(line[0].isnumeric):
                newClause = Clause()
                for word in line.split():
                    #end of clause
                    if(word == '0'):
                        break
                    #specify bool in front of literal
                    var_bool = (word[0]!='-')
                    #specify literal
                    variable = word
                    if(not var_bool):
                        variable = word[1:]
                    newClause.addVariable(variable, var_bool)
                self.clauses.append(newClause)
            else:
                print("ERROR: word ", word, " in line ", line, " unrecognizable")
                quit()
        f.close


    def printSAT(self):
        for clause in self.clauses:
            print("(",clause.stringClause(),") ∧ \n")


    def test_consistance(self,assignments):
        consistent = True
        self.unitaryAssignments = []
        self.variablesUnassiged = dict() # unassigned Var : [satisfiable_value, frequency, is_pure]
        self.partialModelSatisfied = True

        # If there are no Assignments yet
        if(len(assignments)==0):
            self.partialModelSatisfied = False
            first_var = list(self.clauses[0].variables.keys())[0] 
            first_value = self.clauses[0].variables[first_var]
            self.variablesUnassiged[first_var] = [first_value, 1, False]
            return True

        for clause in self.clauses:
            nbVarUnassigned = 0
            clauseSatisfied = False
            firstVarUnassignedClause = None

            for var in clause.variables:
                var_assigned = False

                for assignment in assignments:
                    #If Var assigned
                    if(var == assignment[0]):
                        var_assigned = True
                        #check if it satisfies the clause
                        clauseSatisfied = clauseSatisfied or clause.getValue(var, assignment[1])
                        break
                
                #If Var NOT assigned
                if(not var_assigned):
                    nbVarUnassigned = nbVarUnassigned + 1
                    #put var in unassigned list with potential value that will satisfy clause, its frequency and sign
                    if(var in self.variablesUnassiged):
                        var_sign_in_clause = clause.variables[var]
                        satisfiable_value, frequency, is_pure = self.variablesUnassiged[var]
                        self.variablesUnassiged[var] = [satisfiable_value, frequency+1, is_pure==var_sign_in_clause]
                    else:
                        var_sign_in_clause = clause.variables[var]
                        self.variablesUnassiged[var] = [clause.variables[var], 1, var_sign_in_clause]
                    #If first unassigned Var in Clause
                    if(firstVarUnassignedClause == None):
                        firstVarUnassignedClause = var

            #calculate partial model satisfaction
            self.partialModelSatisfied = self.partialModelSatisfied and clauseSatisfied

            # All Vars assigned and still Clause false
            if(not clauseSatisfied):
                if(nbVarUnassigned == 0):
                    consistent = False

            #Save unitary Clause
            if (nbVarUnassigned == 1 and not clauseSatisfied):
                sign = clause.variables[firstVarUnassignedClause]
                if(sign):
                    self.unitaryAssignments.append([firstVarUnassignedClause, True, None])
                else:
                    self.unitaryAssignments.append([firstVarUnassignedClause, False, None])

        return consistent


    # method 1 - Assignes first unissigned var X to (X, v, v')
    # method 2 - Assignes every var from unitary clause or assignes first unissigned var
    # method 3 - Assignes the variable most frequent first
    def choose(self, assignments, method):
        if(method == 1):
            # First unassigned
            var = list(self.variablesUnassiged.keys())[0]
            return [var,True,False]
        elif(method == 2):
            #Unitary
            if(len(self.unitaryAssignments)!=0):
                return self.unitaryAssignments.pop()
            else:
                # Primary
                for var in self.variablesUnassiged.keys():
                    satisfiable_value, frequency, is_pure = self.variablesUnassiged[var]
                    if(is_pure or frequency==1):
                        return [var, satisfiable_value, not satisfiable_value]
                # Max Occurence
                var = list(self.variablesUnassiged.keys())[0]
                return [var,True,False]

        elif(method == 3):
            #Unitary 
            if(len(self.unitaryAssignments)!=0):
                return self.unitaryAssignments.pop()
            else:
                #Primary
                for var in self.variablesUnassiged.keys():
                    satisfiable_value, frequency, is_pure = self.variablesUnassiged[var]
                    if(is_pure or frequency==1):
                        return [var, satisfiable_value, not satisfiable_value]
            # Max Occurence
            var_max   = list(self.variablesUnassiged.keys())[0]
            satisfiable_value_max, frequency_max, is_pure_max = self.variablesUnassiged[var_max]
            for var in self.variablesUnassiged.keys():
                satisfiable_value, frequency, is_pure = self.variablesUnassiged[var]
                if(frequency>frequency_max):
                    frequency_max = frequency
                    var_max = var
            return [var_max,True,False]


    def backtrack(self, method, findAllSolutions):
        nb = self.nbVariables
        done = False
        all_S = []
        S = []
        while(not done):
            findNextSolution = False
            consistant = self.test_consistance(S)
            if(consistant):
                if(len(S) == nb or self.partialModelSatisfied):
                    all_S.append(S.copy())
                    if(findAllSolutions):
                        findNextSolution = True
                    else:
                        done = True
                else:
                    S.append(self.choose(S, method))
            if(not consistant or findNextSolution):
                self.nb_2b = self.nb_2b + 1
                sol = S.pop()
                while(len(S)>0 and sol[2] == None):
                    sol = S.pop()
                if(sol[2] != None):
                    S.append([sol[0], sol[2], None])
                else:
                    done = True
        return all_S


    def getAssignmentForVar(self, var, all_solutions):
        for assignments in all_solutions:
            for assignment in assignments:
                if(assignment[0] == var):
                    return assignment[1]
        print("ERROR: Variable ", var, " does not have an assignment")
        quit()


    def printSolutions(self, all_solutions):
        if(all_solutions):
            for i in range(len(all_solutions)):
                if(len(all_solutions[i]) == self.nbVariables):
                    print(all_solutions[i])
                    print("SATISFIABLE \n")
                else:
                    print(all_solutions[i])
                    print("SATISFIABLE")
                    print("PARTIAL MODEL \n")
        else:
            print("INSATISFIABLE \n")
       

###################################################

def main(argv):
    # DataBase
    file_20 = "data/uf20-01.cnf"
    file_50 = "data/uf50-01.cnf"
    file_50_not = "data/uuf50-05.cnf"
    file_100  = "data/jnh1.cnf"
    file_test = "data/test.cnf"

    # Initial file and method set up
    file_name = "tp_SAT_eval_F16/sat6.cnf"
    method    = 3
    findAllSolutions = False

    # File name and method if specified
    if(len(argv) == 3):
        file_name = argv[0]
        if(argv[1]=="1" or argv[1]=="2" or argv[1]=="3"):
            method = int(argv[1])
        else:
            print("ERROR: 3rd argument can be only 1/2/3. You entered ", argv[1])
            quit()
        if(argv[2] == "yes"):
            findAllSolutions = True
        elif(argv[2]=="no"):
            findAllSolutions = False
        else:
            print("ERROR: 4th argument can be only yes/no. You entered ", argv[2])
            quit()

    # Set up SAT
    sat = SAT()
    sat.readSATFile(file_name)
    #sat.printSAT()

    # Run algorithm
    start_time = time.time()
    all_solutions = sat.backtrack(method, findAllSolutions)
    end_time = (time.time() - start_time)

    # Print Solution
    sat.printSolutions(all_solutions)
    print(end_time)
    
    # Print value of specific literal
    # print(sat.getAssignmentForVar("18", all_solutions))
    

if __name__ == "__main__":
    main(sys.argv[1:])
    
