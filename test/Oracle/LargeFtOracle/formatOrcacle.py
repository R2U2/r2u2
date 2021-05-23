from io import open

for i in range (0,4):
    filename = 'LargeFT_formula' + str(i)
    f = open(filename + '.csv','r').read()
    lines = f.split('\n')
    f = open(filename + '.txt','w')
    try:
        for line in lines:
            p = line.split(',')
            if(p[1] != ""):
                if(p[1] != '#VALUE!'):
                    f.write(line+'\n')
                    f.flush()
    except EOFError:
        pass
    f.close()
