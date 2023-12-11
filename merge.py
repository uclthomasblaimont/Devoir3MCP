def merge(array1 ,array2):

    len1 = len(array1)
    len2 = len(array2)
    total_len = len1+len2

    print(len1 + len2)
    print(total_len)

    i = 0 
    j = 0
    k = 0

    new_array = [0]*total_len


    while i < len1  and j < len2  :

        if array1[i] <= array2 [j]:
            print( "je place un élément de i dans le nouveau tableau")
            new_array[k] = array1[i]
            i = i+1
        else:
            print("je place un élément de j dans le nouveau tableau")
            new_array[k] = array2[j]
            j = j+1
        k = k +1

    while i < len1 :
        print("--")
        print(k)
        new_array[k] = array1[i]
        i = i + 1
        k = k + 1
        

    while j < len2 :
        print("---")
        print(k)
        new_array[k]  = array2[j]
        j = j + 1
        k = k + 1 

    print(new_array)

    return new_array  

merge([1,2],[3,4])

