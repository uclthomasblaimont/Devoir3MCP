def merge(array1, array2):
    # Longueurs des tableaux entrants
    len1 = len(array1)
    len2 = len(array2)
    total_len = len1 + len2

    # Affichage des longueurs pour le débogage
    print(len1 + len2)
    print(total_len)

    # Initialisation des indices pour le parcours des tableaux
    i, j, k = 0, 0, 0

    # Initialisation du nouveau tableau qui accueillera les éléments fusionnés
    new_array = [0] * total_len

    # Parcourir les deux tableaux et fusionner les éléments
    while i < len1 and j < len2:
        # Comparaison des éléments des deux tableaux
        if array1[i] <= array2[j]:
            # Ajout de l'élément de array1 dans new_array
            print("je place un élément de i dans le nouveau tableau")
            new_array[k] = array1[i]
            i += 1
        else:
            # Ajout de l'élément de array2 dans new_array
            print("je place un élément de j dans le nouveau tableau")
            new_array[k] = array2[j]
            j += 1
        k += 1

    # Ajouter les éléments restants de array1, si nécessaire
    while i < len1:
        print("--")
        print(k)
        new_array[k] = array1[i]
        i += 1
        k += 1

    # Ajouter les éléments restants de array2, si nécessaire
    while j < len2:
        print("---")
        print(k)
        new_array[k] = array2[j]
        j += 1
        k += 1 

    # Affichage du tableau fusionné pour le débogage
    print(new_array)

    # Retourner le tableau fusionné
    return new_array  

# Appel de la fonction merge avec deux tableaux en exemple
merge([1, 2], [3, 4])
