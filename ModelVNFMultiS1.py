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

def VNFMultiS():
    
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
    
    #Set of services
    model.S=RangeSet(model.nb_f)
    model.S1=RangeSet(model.nb_f+1)
    

    #Set of module
    model.L=RangeSet(model.nb_m)

    #Set of nodes
    model.N=RangeSet(model.nb_n)

    #Set of demands
    model.D=RangeSet(model.nb_d)
    
    # Arcs
    model.A=Set(within=model.N*model.N) 

    #Demand parameters
    model.o = Param(model.D,within=NonNegativeIntegers)
    model.t = Param(model.D,within=NonNegativeIntegers)
    model.d = Param(model.D,within=NonNegativeIntegers)
    
    #Parameter of fixe order
    #f is a bidimentional matrix, indexes are demand and VNF position
    # the value is the VNF type that is in a given position for the demand
    model.f=Param(model.D,model.S,within=model.F) #BA: 
    
    #Assignment and location variables
    model.Y=Var(model.N,model.F,model.L,within=Binary)
    model.Z=Var(model.N,model.D,model.F,within=Binary)
    
    #Routing variables
    model.X=Var(model.A,model.D,model.S1,within=Binary)
   
    #Add Constraint
    #model.Const=ConstraintList() #BA Why this?!

    
    #objective function
    def SP(model):
        value=sum(l*model.Y[i,f,l] for l in model.L for f in model.F for i in model.N)
        return value
    
    model.cost = Objective(rule=SP, sense=minimize)
    

    # constraint 1 : each demand to be assigned to one service
    def D_to_S(model,k,f): 
        return sum(model.Z[i,k,f] for i in model.N) == 1

    model.Demand_Service = Constraint(model.D,model.F,rule= D_to_S)
    
     # constraint 2 : a demand is assigned to a node only if a service instance is located on the node
    def D_to_S_Node(model,i,k,f):
        return model.Z[i,k,f] <= sum(model.Y[i,f,l] for l in model.L)
    
    model.Demand_Service_node = Constraint(model.N,model.D,model.F,rule= D_to_S_Node)

    model.nb_f_mod=RangeSet(2,model.nb_f)

    #Constraint 3 : Order
    def routing_subpaths(model,i,k,s):
        value=sum(model.X[i,j,k,s] for j in model.N if (i,j) in model.A)- sum(model.X[j,i,k,s] for j in model.N if (i,j) in model.A)
        return value == model.Z[i,k,model.f[k,s-1]]-model.Z[i,k,model.f[k,s]]

    model.routing_subpaths_Const=Constraint(model.N,model.D,model.nb_f_mod,rule=routing_subpaths)

    
    # constraint 4 :  the link capacity constraints #range(1,model.nb_f+1)
    def Link_Capacity(model,i,j):
        value=[]
        value=sum(sum(model.d[k]*(model.X[i,j,k,s]) for s in model.S1) for k in model.D)
        return value <= model.uu

    model.Link_capacity_const = Constraint(model.A,rule= Link_Capacity)

    # constraint  5:   a simple path is used to route each demand
    def routing_first_subpath(model,i,k):
        value=sum(model.X[i,j,k,1] for j in model.N if (i,j) in model.A) - sum(model.X[j,i,k,1] for j in model.N if (i,j) in model.A)

        if i == model.o[k] :
            return value == 1-model.Z[i,k,model.f[k,1]]
        else :
            return value == -model.Z[i,k,model.f[k,1]]
        
    model.routing_first_subpath_const = Constraint(model.N,model.D,rule= routing_first_subpath)
    
    # constraint  6:   a simple path is used to route each demand
    def routing_last_subpath(model,i,k):
        value = sum(model.X[i,j,k,model.nb_f] for j in model.N if (i,j) in model.A) - sum(model.X[j,i,k,model.nb_f] for j in model.N if (i,j) in model.A)
        if i == model.t[k] :
            return value == model.Z[i,k,model.f[k,model.nb_f]]-1
        else :
            return value==model.Z[i,k,model.f[k,model.nb_f]]

    model.routing_last_subpath_const = Constraint(model.N,model.D,rule= routing_last_subpath) 
    

    # constraint  7:   forbid the two paths to both enter #range(1,model.nb_f+1)
    def simple_path1(model,i,k):
        value = sum(sum(model.X[j,i,k,s] for j in model.N if (i,j) in model.A) for s in model.S1)
        return value <= 1
    
    model.simple_path1_const = Constraint(model.N,model.D,rule= simple_path1)
    
     # constraint  8:   forbid the two paths to both enter #range(1,model.nb_f+1)
    def simple_path2(model,i,k):
        value=sum(sum(model.X[i,j,k,s] for j in model.N if (i,j) in model.A) for s in model.S1)
        return value <= 1

    model.simple_path2_const = Constraint(model.N,model.D,rule= simple_path2)
    
    # constraint 9 :  
    def service_capacity(model,i,f):
        value=sum(model.d[k]*model.Z[i,k,f] for k in model.D)
        return value <= model.mu*sum(l*model.Y[i,f,l] for l in model.L)

    model.service_capacity_const = Constraint(model.N,model.F,rule= service_capacity)
    
   # constraint  10:    limit the amount of demand served by each service instance and link the opening and assignment variables.
    def single_level(model,i,f):
        value=sum(model.Y[i,f,l] for l in model.L)
        return value<= 1

    model.single_level_const = Constraint(model.N,model.F,rule= single_level)

    #constraint 11:
    def node_capacity(model,i):
        value=sum(model.mu*sum(l*model.Y[i,f,l] for l in model.L) for f in model.F)
        return value <= model.nu
    
    model.node_capacity_Const=Constraint(model.N,rule=node_capacity)
    return model

def main():
    # chosing the solver
    optsolver =  create_solver()

    #Creating the model
    model = VNFMultiS()

    #Load the data file (and create an instance)
    instance = model.create_instance('abilene_s_s_l_l.dat')
    starttime=time.time()
    #instance.pprint()
    #solving the problem
    optsolver.options['timelimit'] = 120
    results = optsolver.solve(instance)
    if (results.solver.status == SolverStatus.ok) and (results.solver.termination_condition == TerminationCondition.optimal):
        objective =  getObjectiveValue(instance)
        print("Optimal solution found with value ", objective)
        filename = open("abilene_s_s_l_l.txt",'w')
        printObjectiveValue(instance, filename)
        printPointFromModel(instance, filename)
        filename.close()
        print("le temps d'exécution est ",time.time()-starttime)
    else:
         print("Some problem occurred. Solver terminated with condition ", results.solver.termination_condition)
    #printPointFromModel(instance)
    
if __name__ == '__main__':    

    main()

