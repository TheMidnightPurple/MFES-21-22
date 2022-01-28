from z3 import *

#caso seja ficheiro
def read_file():
    file = input("Insira o nome do ficheiro: ")
    f = open(file, "r")
    levels = int(f.readline())

    s = Solver()
    x = {}
    line = 0

    #decarar variáveis e seus limites
    for i in range(2*levels-1):
        column = 0
        l = f.readline().rstrip().split(" ")#remover "\n" e separar variáveis
        x[line] = {}
        for j in range(len(l)):
            if (i%2 == 0):
                if (l[j] != "-"):
                    if (l[j] != "<" and l[j] != ">"):
                        if not l[j].isnumeric():
                            x[line][column] = Int('x'+str(line)+str(column))
                            s.add(And(1<= x[line][column], x[line][column]<=levels)) #declarar variáveis
                            column+=1
                        else:
                            x[line][column] = Int('x'+str(line)+str(column))
                            s.add(x[line][column] == l[j]) #tipo x00 == 2
                            column+=1
            else:
                column+=1
        if (i%2 == 0):
            line+=1

    #voltar ao início do ficheiro
    f.seek(0)
    f.readline()

    #condições de desigualdade
    for i in range(2*levels-1):
        l = f.readline().rstrip().split(" ")#remover "\n" e separar variáveis
        for j in range(2*levels-1):
            if (i%2 == 0):
                if (l[j] == ">"):
                    i1 = int(i/2)
                    j1 = int((j-1)/2)
                    j2 = int((j+1)/2)
                    s.add(x[i1][j1] > x[i1][j2])
                else:
                    if (l[j] == "<"): 
                        i1 = int(i/2)
                        j1 = int((j-1)/2)
                        j2 = int((j+1)/2)
                        s.add(x[i1][j2] > x[i1][j1])
            else:
                if (l[j] == ">"):
                    j1 = int(j/2)
                    i1 = int((i-1)/2)
                    i2 = int((i+1)/2)
                    s.add(x[i1][j1] > x[i2][j1])
                else:
                    if (l[j] == "<"):
                        j1 = int(j/2)
                        i1 = int((i-1)/2)
                        i2 = int((i+1)/2)
                        s.add(x[i2][j1] > x[i1][j1])

    #rstrições de linha
    for i in range(len(x)):
        for j in range(len(x[i])-1):
            for k in range(len(x)):
                if (j != k):
                    s.add(Distinct(x[i][j], x[i][k]))#restrições de linha
                    s.add(Distinct(x[j][i], x[k][i]))#restrições de coluna

    if s.check() == sat:
        m = s.model()
        print(m)
    else:
        print("\nUNSAT")


#caso seja string
def read_string():
    
    tabuleiro = input('Insira o tabuleiro em forma de String:')
    li = tabuleiro.replace(r'\n', '\n').split("\n")
    levels = int(li[0])

    lines = tabuleiro.replace(r'\n', '\n').split("\n")[1:]#retirar o level

    s = Solver()
    x = {}
    line = 0
    
    #decarar variáveis e seus limites
    for i in range(2*levels-1):
        column = 0
        l = lines[i].rstrip().split(" ")#remover "\n" e separar variáveis
        x[line] = {}
        for j in range(len(l)):
            if (i%2 == 0):
                if (l[j] != "-"):
                    if (l[j] != "<" and l[j] != ">"):
                        if not l[j].isnumeric():
                            x[line][column] = Int('x'+str(line)+str(column))
                            s.add(And(1<= x[line][column], x[line][column]<=levels)) #declarar variáveis
                            column+=1
                        else:
                            x[line][column] = Int('x'+str(line)+str(column))
                            s.add(x[line][column] == l[j]) #tipo x00 == 2
                            column+=1
            else:
                column+=1
        if (i%2 == 0):
            line+=1

    #condições de desigualdade
    for i in range(2*levels-1):
        l = lines[i].split(" ")#remover "\n" e separar variáveis
        for j in range(2*levels-1):
            if (i%2 == 0):
                if (l[j] == ">"):
                    i1 = int(i/2)
                    j1 = int((j-1)/2)
                    j2 = int((j+1)/2)
                    s.add(x[i1][j1] > x[i1][j2])
                else:
                    if (l[j] == "<"): 
                        i1 = int(i/2)
                        j1 = int((j-1)/2)
                        j2 = int((j+1)/2)
                        s.add(x[i1][j2] > x[i1][j1])
            else:
                if (l[j] == ">"):
                    j1 = int(j/2)
                    i1 = int((i-1)/2)
                    i2 = int((i+1)/2)
                    s.add(x[i1][j1] > x[i2][j1])
                else:
                    if (l[j] == "<"):
                        j1 = int(j/2)
                        i1 = int((i-1)/2)
                        i2 = int((i+1)/2)
                        s.add(x[i2][j1] > x[i1][j1])

    #rstrições de linha
    for i in range(len(x)):
        for j in range(len(x[i])-1):
            for k in range(len(x)):
                if (j != k):
                    s.add(Distinct(x[i][j], x[i][k]))#restrições de linha
                    s.add(Distinct(x[j][i], x[k][i]))#restrições de coluna

    if s.check() == sat:
        m = s.model()
        print(m)
    else:
        print("\nUNSAT")

    

while True:
    option = input("1 - Ler Ficheiro | 2 - Ler String: ")  
    if (option == "1"):
        read_file()
        break
    else:
        if(option == "2"):
            read_string()
            break
        else:
            print("Opção inválida!")