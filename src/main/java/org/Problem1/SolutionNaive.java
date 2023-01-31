/*
    Created, specified and implemented by Henri GEVENOIS
    As part of the course of algorithmics II at University of Namur
 */
package org.Problem1;

import Problem1.DataInit.InvalidInputException;
import Problem1.DataInit.Name;
import Problem1.DataInit.SFile;

public class SolutionNaive
{
    /*
        @               public normal_behavior
        @ requires      (* n ∈ s_file : 0 < n < Integer.MAX_VALUE);
        @ requires      (* n == #S == #M);
        @ requires      (* M ∈ s_file : (\typeof(M) == \elemtype(int[]) && M != null && \for all int i; 0 <= i < n; 0 < M[i] < Integer.MAX_VALUE *);
        @ requires      (* S ∈ s_file : (\typeof(S) == \elemtype(String[][]) && S != null && \for all int i; 0 <= i < n; (\for all j; 0 <= j < M[i]; S[i][j] != null *);
        @ requires      (InvalidInputException e) false (* new FileInputValidation(s_file).validateObject() must pass *);
        @
        @ ensures		\result == null === true;
        @ ensures       Solution.length == SFILE.getN();
        @ ensures       \for all int i; 0 <= i && i < SFILE.getN();
        @                   (\for all int j; 0 <= j && j < SFILE.getM()[i];
        @                       (\exists int k; 0 <= k && k < SFILE.getM()[i];
        @                           && (\num_of int l; 0 <= l && l < SFILE.getM()[i]; SFILE.getS_atIndex(i)[k].equals(SFILE.getS_atIndex(i)[k])) > SFILE.getM()[i] / 2)))
        @                               ==> (\result[i] == SFILE.getS_atIndex(i)[k]))
        @                   &&  (\for all int k; 0 <= k && k < SFILE.getM()[i]; SFILE.getS_atIndex(i)[k]
        @                           && (\num_of int l; 0 <= l && l < SFILE.getM()[i]; (SFILE.getS_atIndex(i)[k].equals(SFILE.getS_atIndex(i)[k])) <= SFILE.getM()[i] / 2)))
        @                               ==> (\result[i] == null));
        @
        @ pure
        @
        @ also          public exceptional_behavior
        @ requires      s_file == null;
        @ ensures       \result <==> null;
        @ signals_only  NullPointerException, ArrayIndexOutOfBoundsException, InvalidInputException;
        @ signals       (InvalidInputException e) true;
     */

    /**
     * Complexity   => O(n²/2) + O(n³), so that a cubic complexity
     */
    public static /*@ nullable */ String[] Naive(String s_file)
    {
        /* @ nullable */ String[] Solution = new String[0];
        try
        {
            SFile SFILE = new SFile(s_file);        // O(n²/2)
            int N = SFILE.getN();                   // O(1)

            /* @ nullable */ Solution = new String[SFILE.getN()]; //O(1)

            /*
                @ loop_invariant    0 <= i && i < N;
                @ loop_invariant    \for all int j; 0 <= j && j < i;
                @                       (\exists int k; 0 <= k && k < M[j]; S.get(j)[k]
                @                           (\num_of int l; 0 <= l && l < M[j]; S.get(l)[k].equals(S.get(j)[k])) > ((double) M[j]) / 2)
                @                               ==> Solution[j].equals(S.get(j)[k]))
                @                   &&  (\for all int k; 0 <= k && k < M[j]; S.get(j)[k]
                @                           (\num_of int l; 0 <= l && l < M[j]; S.get(l)[k].equals(S.get(j)[k])) <= ((double) M[j]) / 2)
                @                               ==> Solution[j] == null);
                @ decrease          N - i;
            */
            for (int i = 0; i < N; i++) // O(n)
            {
                Solution[i] = getMostFrequentName(SFILE.getS_toName_atIndex(i), SFILE.getM()[i]); // O(n²)
            }
            return Solution;
        }
        catch (NullPointerException | ArrayIndexOutOfBoundsException | InvalidInputException e)
        {
        	return null;
        }
    }

    /*
        @               public normal_behavior
        @ requires      m == names.length;
        @ requires      names != null && \for int i; 0 <= i && i < m; names[i] != null;
        @ ensures       names <==> \old(names);
        @ ensures       m <==> \old(m);
        @ ensures       \result <==> names[i][k] ==>   \for all int i; 0 <= i && i < m;
        @                                               (\exists int j; 0 <= j && j < m;
        @                                                   (\num_of int k; 0 <= k && k < m; names[i][k].equals(names[j][k])) > ((double) m) / 2));
        @ ensures       \result <==> null ==>       \for all int i; 0 <= i && i < m;
        @                                               (\for all int j; 0 <= j && j < m;
        @                                                   (\num_of int k; 0 <= k && k < m; names[i][k].equals(names[j][k])) <= ((double) m) / 2));
        @
        @               public exceptional_behavior
        @ signals       (ArrayIndexOutOfBoundsException | NullPointerException e) true;
        @ pure
     */

    /**
     * Complexity   => O(n²), since two nested loops
     */
    public static /*@ nullable */ String getMostFrequentName(Name[] names, int m)
    {
        try
        {
            String MostCurrentName;
            int indexOfMostCurrentName = 0;
            int counterMax = 0;
            int counterTemp;

            /*
            	@ loop_invariant	m <==> \old(m);
            	@ loop_invariant    MostCurrentName <==> \old(MostCurrentName);
            	@ loop_invariant    names <==> \old(names);
            	@ loop_invariant    0 <= i < m;
            	@ loop_invariant    0 <= counterTemp <= m;
            	@ loop_invariant    0 <= counterMax <= m;
            	@ loop_invariant	\for all int p; 0 <= a < i; ((counterMax < counterTemp) ==> (counterMax == counterTemp) && (indexOfMostCurrentName = p))
            	@											&&	((counterMax >= counterTemp) ==> counterMax == \old(counterMax));
            	@ decrease			m - i;
             */
            for (int i = 0; i < m; i++)
            {
                counterTemp = 0;
                /*
                    @ loop_invariant    m <==> \old(m);
                    @ loop_invariant    names <==> \old(names);
                    @ loop_invariant	0 <= counterTemp <= m;
                    @ loop_invariant    0 <= counterMax <= m;
                    @ loop_invariant    0 <= i < m;
                    @ loop_invariant    0 <= j < m;
                    @ loop_invariant    \for all int p; 0 <= p && p < i;
                    @                       (\exists int q; 0 <= q && q < j;
                    @                           (\num_of int k; 0 <= k && k < j; names[p][k].equals(names[q][k])) == counterTemp);
                    @ decrease          m - j;
                 */
                for (int j = 0; j < m; j++)
                {
                    if(names[i].getHashCode() == names[j].getHashCode() && counterTemp < Integer.MAX_VALUE)
                        counterTemp++;
                }
                if(counterMax < counterTemp)
                {
                    counterMax = counterTemp;
                    indexOfMostCurrentName = i;
                }
            }
            if(counterMax <= ((double) m)/2)
                return null;
            else {
                MostCurrentName = names[indexOfMostCurrentName].getName();
            }
            return MostCurrentName;
        }
        catch (ArrayIndexOutOfBoundsException | NullPointerException e)
        {
            throw e;
        }
    }
}
