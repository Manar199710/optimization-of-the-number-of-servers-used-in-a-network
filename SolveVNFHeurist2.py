from pyomo.environ import *
from pyomo.opt import SolverFactory
from pyomo.opt import SolverStatus, TerminationCondition

from ModelVNFHeurist2 import *
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
def DFRHeurist(file,time_limit):
    #Creation de solveur
    optsolver =  create_solver()
    
    #create model
    model=VNFHeurist(1) 
    
    #create model
    instance = model.create_instance(file+".dat")#create
    
    time_start = time.time()#initialisation du temps
    
    #Déclaration  les valeurs des variables
    VNFmin = int(instance.nb_n.value/4)
    stop =False
    
    #la boucle pour trouver la solution
    while stop == False:
        
        VNFfix = int((instance.nb_n.value+VNFmin)/2)#Actualiser la valeur de la VNF
        
        model=VNFHeuristR(VNFfix) #create model relaxer
        instance = model.create_instance(file+".dat")#create instance
        results = optsolver.solve(instance)# resolve problem
        res=(getObjectiveValue(instance))/3 # objective
        print("l")
        if res == instance.nb_d.value:
            print("d")
            #Résolution avec le modèle sans relaxation
            model1=VNFHeurist(VNFfix) #create model
            instance1 = model1.create_instance(file+".dat")#create
            results1 = optsolver.solve(instance1)# resolve problem
            res1=(getObjectiveValue(instance1))/3 
            
            if res1 == instance1.nb_d.value: # pour être sur du résultat avec le problème non relaxer
                stop = True
            
        #Si nous atteindrons les limites
        if time.time()-time_start > time_limit or VNFfix >= instance.nb_n.value : 
            print("Reach the limit")
            stop = True

        VNFmin = VNFfix

    # Calcule de la solution
    if stop == True:
        print("solution trouver")
        model1=VNFHeurist(VNFfix) #create model avec la VNffix actualiser
        instance1 = model1.create_instance(file+".dat")#create model
        results1 = optsolver.solve(instance1)# resolve problem
        res1=getObjectiveValue(instance1)#Get the objective
        #Enregistrer les données dans un fichier Txt
        filename = open("resultat heureustique2.txt",'w')
        printObjectiveValue(instance1, filename)
        printPointFromModel(instance1, filename)
        filename.close()
        a=0
        for i in instance.N_a:
            for f in instance.F:
                for l in instance.L:
                    a=a+instance.Y[i,f,l].value
        print("le temps d'exécution",time.time()-time_start)
        return print("la solution est ",a)
    else:
        #Si nous avons échoué de trouver la solution
        if time.time()-time_start < time_limit:
            print("Solution echouer")
            #Nous commencons tout d'abord une résolution normale pour prendre les noeuds que nous mettons en service
            model2 =VNFMultiS(instance1.nb_n.value)
            instance2 = model2.create_instance(file+".dat")#create
            results2 = optsolver.solve(instance2)# resolve problem
            res2=getObjectiveValue(instance2)
            
            C=[] # les noeuds en services
            L=[] # les noeuds hors services
            
            #Extraire les noeuds en services et hors services
            for i in instance2.N.value:
                for f in instance2.F.value:
                    for l in instance2.L.value:
                        if instance2.Y[i,f,l].value==1:
                            C.append(i)
                        else:
                            L.append(i)
                            
            #Add constraint limiting the location changes
            instance2.limit.add(sum(1-instance2.Y[i,f,l].value for i in C for f in instance2.F.value for l in instance2.L.value)+sum(Y[i,f,l] for i in L for f in instance2.F.value for l in instance2.L.value)<=int(instance2.nb_n.value/10))
            #Résoudre le modèle en prenant en considération la contrainte
            results2 = optsolver.solve(instance2)# resolve problem
            res2=getObjectiveValue(instance2)
            #Enregistrement des résultats dans un fichier txt
            filename = open("resultat heureustique2.txt",'w')
            printObjectiveValue(instance2, filename)
            printPointFromModel(instance2, filename)
            filename.close()
            print("le temps d'exécution",time.time()-time_start)
            return print("le nombre de demande servi avec l'heuristique est ",res2)
        
        return print("No feasuble solution found")
    
def main():
    # file 
    file = "ta1_s_s_m_l" #atlanta_s_s_h_l
    time_limit = 1200
    DFRHeurist(file,time_limit)
    
if __name__ == '__main__':    

    main()
            
        
        

            