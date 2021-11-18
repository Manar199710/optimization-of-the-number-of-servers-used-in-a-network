from pyomo.environ import *
from pyomo.opt import SolverFactory
from pyomo.opt import SolverStatus, TerminationCondition
import time


### Auxiliary code ###
###This part allows to have a "machine-independent" code if some conventions are respected

import os, sys
sys.path.insert(0,os.path.abspath(os.path.join(os.path.dirname(__file__),'../utilities')))
from optmodel_utilities import *

def create_solver(solver_name = 'cplex'):
    solver_path = get_solver_path(solver_name)
    return  SolverFactory(solver_name, executable=str(solver_path), solver_io = 'nl')    

#
# Model
#

def VNFHeurist1(VNFix):
    
    infinity = float('inf')
    
    model = AbstractModel()
    
    #number of services
    model.nb_f=Param()
    
    #Set of service type
    model.F=Set()
    
    #number of possible module
    model.nb_m=Param()
    
    # arc capacity
    model.uu = Param()

    #capacity of each module
    model.mu =Param()
    
    # nodes capacity
    model.nu = Param()
    
    #number of nodes
    model.nb_n=Param()
    
    #number of demand
    model.nb_d=Param()
    
    #auxiliaire node
    model.a=Param(default=0)
    
    model.a_set = RangeSet(model.a,model.a)
    
    #Set of services
    model.S=RangeSet(model.nb_f)
    model.S1=RangeSet(model.nb_f+1)
    

    #Set of module
    model.L=RangeSet(model.nb_m)

    #Set of nodes
    model.N=RangeSet(model.nb_n)
    
    #Set of nodes union {a}
    model.N_a = RangeSet(0,model.nb_n)
    #model.N_a = Set(model.N | model.a)
    
    #Set of demands
    model.D=RangeSet(model.nb_d)
    
    # Arcs
    model.A=Set(within=model.N*model.N) 
    
    model.all_a=Set(initialize=model.N*model.a_set)
    
    model.a_all=Set(initialize=model.a_set*model.N)
    #Arcs union {a}
    #model.AMD=Set(within=model.N_a*model.N_a)
    model.AMD=model.all_a | model.a_all | model.A

    #Demand parameters
    model.o = Param(model.D,within=NonNegativeIntegers)
    model.t = Param(model.D,within=NonNegativeIntegers)
    model.d = Param(model.D,within=NonNegativeIntegers)
    
    #Parameter of fixe order
    #f is a bidimentional matrix, indexes are demand and VNF position
    # the value is the VNF type that is in a given position for the demand
    model.f=Param(model.D,model.S,within=model.F) #BA: 
    
    #Assignment and location variables
    model.Y=Var(model.N_a,model.F,model.L,within=Binary)
    model.Z=Var(model.N_a,model.D,model.F,within=Binary)
    
    #Routing variables
    model.X=Var(model.AMD,model.D,model.S1,within=Binary)

    #Add Constraint
    #model.Const=ConstraintList() #BA Why this?!
    
    #objective function
    def SP(model):
        value=sum(model.Z[i,k,f] for i in model.N for k in model.D for f in model.F)
        return value
    
    model.cost = Objective(rule=SP, sense=maximize)
    
    #constraint 1 : each demand to be assigned to one service
    def D_to_S(model,k,f): 
        return sum(model.Z[i,k,f] for i in model.N_a) == 1

    model.Demand_Service = Constraint(model.D,model.F,rule= D_to_S)
    
    #Constraint 2 :  a demand is assigned to a node only if a service instance is located on the node
    def D_to_S_Node(model,i,k,f):
        return model.Z[i,k,f] <= sum(model.Y[i,f,l] for l in model.L)
    
    model.Demand_Service_node = Constraint(model.N_a,model.D,model.F,rule= D_to_S_Node)
    
    #Constraint 3 : the link capacity constraints #range(1,model.nb_f+1)
    def Link_Capacity(model,i,j):
        value=[]
        value=sum(sum(model.d[k]*model.X[i,j,k,s] for s in model.S1) for k in model.D)
        return value <= model.uu

    model.Link_capacity_const = Constraint(model.AMD,rule= Link_Capacity)# Ajouter AMD
    
    #Constraint 4 : a simple path is used to route each demand
    def routing_first_subpath(model,i,k):
        value=sum(model.X[i,j,k,1] for j in model.N if (i,j) in model.AMD) - sum(model.X[j,i,k,1] for j in model.N if (i,j) in model.AMD)

        if i == model.o[k] :
            return value == 1-model.Z[i,k,model.f[k,1]]
        else :
            return value == -model.Z[i,k,model.f[k,1]]
        
    model.routing_first_subpath_const = Constraint(model.N_a,model.D,rule= routing_first_subpath)
    
    #Constraint 5 : a simple path is used to route each demand
    def routing_last_subpath(model,i,k):
        value = sum(model.X[i,j,k,model.nb_f] for j in model.N if (i,j) in model.AMD) - sum(model.X[j,i,k,model.nb_f] for j in model.N if (i,j) in model.AMD)
        if i == model.t[k] :
            return value == model.Z[i,k,model.f[k,model.nb_f]]-1
        else :
            return value==model.Z[i,k,model.f[k,model.nb_f]]

    model.routing_last_subpath_const = Constraint(model.N_a,model.D,rule= routing_last_subpath) 
    
    #Constraint 6 : forbid the two paths to both enter #range(1,model.nb_f+1)
    def simple_path1(model,i,k):
        #if not any(model.X[j,i,k,s] for j in model.N if (j,i) in model.AMD for s in model.S1):
         #   return Constraint.Skip
        value = sum(sum(model.X[j,i,k,s] for j in model.N if (j,i) in model.AMD) for s in model.S1)
        return value <= 1
    
    model.simple_path1_const = Constraint(model.N_a,model.D,rule= simple_path1)
    
    #Constraint 7 : forbid the two paths to both enter #range(1,model.nb_f+1)
    def simple_path2(model,i,k):
        #if not any(model.X[i,j,k,s] for j in model.N if (i,j) in model.AMD for s in model.S1):
        #    return Constraint.Skip
        value=sum(sum(model.X[i,j,k,s] for j in model.N if (i,j) in model.A) for s in model.S1)
        return value <= 1

    model.simple_path2_const = Constraint(model.N,model.D,rule= simple_path2)
    
    #Constraint 8 : given the number of installed VNF
    def NbVNF(model,f,l):
        value=sum(model.Y[i,f,l] for i in model.N)
        return value <= VNFix
    
    model.NbVNF_const=Constraint(model.F,model.L,rule = NbVNF)
    
    #Constraint 9 :  using arcs incident in a for routing a demand that is not served by the VNF on a
    def Paths2_a(model,k,f):
        value=sum(sum(model.X[i,model.a.value,k,s] for i in model.N if (i,model.a.value) in model.AMD) for s in model.S1)
        return value <= model.Z[model.a.value,k,f]

    model.Paths2a_const = Constraint(model.D,model.F,rule= Paths2_a)
    
    
    return model

def AFRHeurist(file,Limit):
    # chosing the solver
    optsolver =  create_solver()

    model=VNFHeurist1(1) #create model
        
    instance = model.create_instance(file+".dat")#create
    
    VNFix=instance.nb_n.value
    res1=0


    
    model=VNFHeurist1(VNFix) #create model
        
    instance = model.create_instance(file+".dat")#create
    print("la valeur du n", instance.nb_n.value)
    starttime=time.time()
    while (time.time()-starttime)<Limit :
        results = optsolver.solve(instance)# resolve problem
        res0=(getObjectiveValue(instance))/3 # objective
        print("le nombre de demande",instance.nb_d.value)
        print("Le temps limite",Limit)
        if res0 == instance.nb_d.value:
            results = optsolver.solve(instance) # resolve problem
            filename = open("resultat heureustique.txt",'w')
            printObjectiveValue(instance, filename)
            printPointFromModel(instance, filename)
            filename.close()
            a=0
            for i in instance.N_a:
                for f in instance.F:
                    for l in instance.L:
                        a=a+instance.Y[i,f,l].value
            #a = getObjectiveValue(instance)
            print("Le temps d'exécution ",time.time()-starttime)
            return print("le nombre de demande servi avec l'heuristique pour une fonction est ",a)

        
        if res1< res0 and res0<instance.nb_d.value:
            for i in instance.N:
                for k in instance.D:
                    for f in instance.F:
                        if instance.Z[i,k,f].value == 1:
                            print("instance.Z[i,k,f].value ")
                            instance.Z[i,k,f].fixe() #{ fix Z}
               
            res1 = res0

    return print("No feasible solution found")

def main():
    # file 
    file = "nobel-eu_s_s_h_l"
    Limit= 1200
    AFRHeurist(file,Limit)
    
    
'''
def main():
    # chosing the solver
    optsolver =  create_solver()

    #Creating the model
    model = VNFHeurist1(1)

    #Load the data file (and create an instance)
    instance = model.create_instance('di-yuan_s_s_l_l.dat')
    #instance.pprint()
    #solving the problem
    results = optsolver.solve(instance)

    objective =  getObjectiveValue(instance)
    print("Optimal solution found with value ", objective)
    filename = open("di-yuan_s_s_l_l.txt",'w')
    printObjectiveValue(instance, filename)
    printPointFromModel(instance, filename)
    filename.close()
    #printPointFromModel(instance)
'''
if __name__ == '__main__':    

    main()

