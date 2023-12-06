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




predicate ordered(a: array<int>)
    /* `a[..]` est ordonné. */
    reads a
{
    forall i,j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

predicate ordered_upto(a: array<int>, n: int)
    /* `a[..n]` est ordonné. */
    requires 0 <= n <= a.Length
    reads a
{
    forall i,j | 0 <= i <= j < n :: a[i] <= a[j]
}

predicate ordered_split(a1: array<int>, n1: int, a2: array<int>, n2: int)
    /* a1[..i1] <= a2[i2..] */
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
    reads a1, a2;
{
    multiset(a1[..]) == multiset(a2[..])
}

method merge(a1: array<int>, a2: array<int>) returns (a: array<int>)
    /* fusionne deux tableaux ordonnés `a1` et `a2` en un seul tableau ordonné `a`. */

/* les 2 tableaux doivent être trier 
les 2 arrays != NULL

*/
{
    // A IMPLEMENTER
}

method sort(a: array<int>) returns (b: array<int>)
/*
rajouter les spécifications 

requires a!=null;
requires lo <= m <= hi;
requires 0 <= a1 <= L.Length;
requires 0 <= m <= L.Length;
requires 0 <= a2 <= L.Length;

il faut replacer les requires ?

*/


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