/***
    LINFO1122 - Méthodes de Conception de Programmes
    Devoir 3 - Vérification avec Dafny
    ================================================
    Automne 2023, Charles Pecheur

Pour ce troisième devoir, il vous est demandé de compléter, spécifier et de vérifier 
le programme Dafny ci-dessous.  

Il s'agit d'une implémentation de tri par fusion sur des tableaux. Vous devez implémenter 
la méthode `merge()`.  La méthode principale `sort()` est déjà implémentée.  
Plusieurs prédicats sont également fournis, utilisez-les pour vos spécifications.

Pour être valide, votre code doit pouvoir être vérifié par Dafny. 
- Implémentez la méthode `sort()`. 
- Dans un premier temps, ne vous occupez pas du code de test (fonction 
`Main()`).  L'annotation `{:verify false}` court-circuite la vérification, 
vous pourrez l'enlever par la suite. 
- Ajoutez les spécifications nécessaires (requires, reads, modifies, fresh, 
invariants) pour résoudre toute les erreurs reportées par Dafny.  
- Complétez les spécifications des méthodes.  Travaillez progressivement, en apportant à 
chaque fois les corrections et ajouts nécessaires pour que la vérification 
réussisse.
- Quand vos spécifications seront complètes, activez la vérification de la 
fonction `Main()` (en supprimant le `{:verify false}`) et complétez
si nécessaire vos spécifications.  Enfin, vous pouvez compiler et exécuter 
votre programme (dans VS-Code, clic droit > Dafny > Run).

Idéalement, toutes vos spécifications doivent être vérifiables.  
Commentez et annotez comme suit celles qui ne le seraient pas:

    // FAILS: ensures world_is_enough()

Votre code sera votre rapport. Pensez à détailler les problèmes rencontrés
et les choix effectués quand cela est pertinent, sous forme de commentaires
dans le code.

Ce devoir est à remettre pour le **mercredi 20 décembre** sur Moodle.
***/


// poulet

predicate ordered(a: array<int>)
    /* `a[..]` est ordonné. */
    reads a
    requires a != null
{
    forall i,j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

predicate ordered_upto(a: array<int>, n: int)
    /* `a[..n]` est ordonné. */
    requires a != null
    requires 0 <= n <= a.Length
    reads a
{
    forall i,j | 0 <= i <= j < n :: a[i] <= a[j]
}

predicate ordered_split(a1: array<int>, n1: int, a2: array<int>, n2: int)
    /* a1[..i1] <= a2[i2..] */
    requires a1 != null && a2!= null
    requires 0 <= n1 <= a1.Length
    requires 0 <= n2 <= a2.Length
    reads a1, a2
{
    forall i1 | 0 <= i1 < n1 ::
        forall i2 | n2 <= i2 < a2.Length :: 
            a1[i1] <= a2[i2]
}

predicate same_elements(a1: array<int>, a2: array<int>)
    /* `a1[..]` et `a2[..]` contiennent les mêmes éléments. */
    requires a1 != null && a2 != null
    reads a1, a2
    // les multisets sont utiles quand on doit compter le nombre d'occurence des éléments
{
    multiset(a1[..]) == multiset(a2[..])
}

method merge(a1: array<int>, a2: array<int>) returns (a: array<int>)
    /* fusionne deux tableaux ordonnés `a1` et `a2` en un seul tableau ordonné `a`.   
     */


requires a1 != null && a2 != null
requires ordered(a1) && ordered(a2)
ensures a.Length == a1.Length + a2.Length
ensures a != null
ensures ordered(a) 
//ensures same_elements(a,a1 + a2) // il faut demander pq c'est rouge 


{

    var i := 0 ;
    var j := 0 ;
    var k := 0 ;
    var length := a1.Length + a2.Length;
    a := new int[length];


    while i < a1.Length  && j < a2.Length
    invariant 0 <= i <= a1.Length
    invariant 0 <= j <= a2.Length
    invariant 0 <= k <= a.Length
    invariant ordered_upto(a, k)
    // FAIL  invariant same_elements(a[..k],multiset(a1[..i])+multiset(a2[..j]))
    // ^ il faut demander pourqoi cette fonction n'est pas bonne
    
    {
        
        if a1[i] <= a2[j]{
            a[k] := a1[i]; 
            i := i+1;

        }else{
            a[k] := a2[j];
            j:= j+1;
        }
        k:= k + 1;
    }

    


    while i < a1.Length 
    invariant 0 <= i <= a1.Length
    invariant 0 <= k <= a.Length
    invariant ordered_upto(a, k)
    {
        a[k] := a1[i];
        i := i + 1;
        k := k + 1;
    }

    

    while j < a2.Length 
    invariant 0 <= j <= a2.Length
    invariant 0 <= k <= a.Length
    invariant ordered_upto(a, k)
    {
        a[k] := a2[j];
        j := j + 1;
        k := k + 1;
    }
    
}

method sort(a: array<int>) returns (b: array<int>)




requires a!=null;
ensures b != null
ensures ordered(b)
ensures a.Length == b.Length
ensures same_elements(a,b)
    /*  Retourne un tableau ordonné `b` contenant 
        les éléments de `a`. */
{
    if a.Length <= 1 {
        b := a;
    } else {
        var m := a.Length/2;
        var a1 := new int[m];
        var a2 := new int[a.Length-m];
        forall i | 0 <= i < m { a1[i] := a[i]; }
        forall i | 0 <= i < a.Length-m { a2[i] := a[m+i]; }
        assert a1[..]+a2[..] == a[..];
        a1 := sort(a1);
        a2 := sort(a2);
        b := merge(a1, a2);
    }
}

/**
 * Tests
 Ne pas toucher
 */
method {:verify false} Main()
{
    var a := new int[][4,2,3,3,5,1];
    var b := sort(a);
    assert ordered(b);
    assert same_elements(a, b);

    print_array(a);
    print_array(b);


    // Test avec tableau vide
    var emptyArray := new int[0];
    var sortedEmpty := sort(emptyArray);
    assert ordered(sortedEmpty);
    assert same_elements(emptyArray, sortedEmpty);

    // Test avec un seul élément
    var singleElement := new int[1];
    singleElement[0] := 5;
    var sortedSingle := sort(singleElement);
    assert ordered(sortedSingle);
    assert same_elements(singleElement, sortedSingle);

    // Test avec tableau inversé
    var reverseArray := new int[5];
    reverseArray[0] := 5; reverseArray[1] := 4; reverseArray[2] := 3; reverseArray[3] := 2; reverseArray[4] := 1;
    var sortedReverse := sort(reverseArray);
    assert ordered(sortedReverse);
    assert same_elements(reverseArray, sortedReverse);

    // Test avec tableau déjà trié
    var sortedArray := new int[5];
    sortedArray[0] := 1; sortedArray[1] := 2; sortedArray[2] := 3; sortedArray[3] := 4; sortedArray[4] := 5;
    var resortedArray := sort(sortedArray);
    assert ordered(resortedArray);
    assert same_elements(sortedArray, resortedArray);

    // Test avec tableau aléatoire
    var randomArray := new int[5];
    randomArray[0] := 3; randomArray[1] := 1; randomArray[2] := 4; randomArray[3] := 1; randomArray[4] := 5;
    var sortedRandom := sort(randomArray);
    assert ordered(sortedRandom);
    assert same_elements(randomArray, sortedRandom);

    // Afficher les tableaux triés
    print_array(sortedEmpty);
    print_array(sortedSingle);
    print_array(sortedReverse);
    print_array(resortedArray);
    print_array(sortedRandom);
}


/*NE PAS TOUCHER*/


method print_array(a: array<int>)
{
    print "[ ";
    var i := 0;
    while i < a.Length
    {
        print a[i], " ";
        i := i+1;
    }
    print "]\n";
}