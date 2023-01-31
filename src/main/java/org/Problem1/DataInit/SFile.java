/*
    Created, specified and implemented by Henri GEVENOIS
    As part of the course of algorithmics II at University of Namur
 */
package Problem1.DataInit;

import java.util.ArrayList;
import java.util.Scanner;

/**
    @overview   SFILE represent a file .txt n wich the first line consists of a positive integer n, corresponding at the number of test cases,
                For each test case, there are two lines, the first one consists of a positive integer m = number of names,
                and the second one consists of the sequence of names.

                SFILE is imutable
                SFile is a quadruplet <n, M, S> :

                Typical structure of s_file  :
                4
                7
                Leclercq Peeters Martin Peeters Peeters Dubois Peeters
                5
                Peeters Goossens Laurent Goossens Goossens
                3
                Peeters Laurent Wouters
                1
                Leclercq

    @specfield      N       : int                   : Number of test cases
    @specfield      M       : int[]                 : Set {m1, m2, ..., mN} where each element is an integer corresponding at the size of a sequence of names
    @specfiels      S       : ArrayList<String[]>   : Set {s1, s2, ..., sN} where each element is a String[] containing, at each index, a name of the sequence s[i];
    @derivedfield   S_toName: ArrayList<Name[]>     : Set derived of S including, for each element, a field int HashCode and a field int NbOccurences (cfr abstraction of object Name)

                 -> n           : number of tests present in s_file :
                 -> M           : an subset of s_file containing the {m1, m2, ..., mn} where each of their values corresponds of the number of names presents in each S[i]
                 -> S           : an subset of s_file containing the {s1, s2, ..., sn} sets of word that are current names given in Belgium
                 -> S_toName    : cfr spec of Object Name

    @invariant      0 < n && n < Integer.MAX_VALUE
    @invariant      M can't be null && each element int of M > 0 && #M == N
    @invariant      S can't be null && each element String of S can't be null && #S == N
    @invariant      for each element of M, it exists only one sequence of S with a size of the same value

 */

public class SFile
{
    private /* @spec_public */ int N;
    private /* @spec_public */ int[] M;
    private /* @spec_public */ ArrayList<String[]> S;  //Array of names under String form
    private /* @spec_public */ ArrayList<Name[]> S_toName;     //Array of names under Name form (String, HashCode, Occurrences)

    /*
        @ public invariant      0 < N && N < Integer.MAX_VALUE;
        @ public invariant      M != null && M.length == N;
        @ public invariant      \for all int i; 0 <= i && i < N; M[i] > 0 && M[i] < Integer.MAX_VALUE;
        @ public invariant      S != null && S.size() == N;
        @ public invariant      \for all int i; 0 <= i && i < N;
        @                           (\for all int j; 0 <= j && j < M[i]; s.getS_atIndex(i)[j] != null);
        @ public invariant      S_toName != null && S_toName.size == N;
        @ public invariant      \for all int i; 0 <= i && i < N;
        @                           (\for all int j; 0 <= j && j < M[i]; S_toName.getS_toName_atIndex(i)[j] != null);
     */

    /** ---------------- CONSTRUCTORS ---------------- */

    /*
        @                       public normal_behavior
        @ requires              s_file != null;
        @ diverges              true;
        @ assignable            \everything;
        @ ensures               Q;                                      // !!!! à faire !!!!
        @ signals_only          InvalidFileStructureException;
     */

    /**
     * Complexity => O(n²/2)
     */
    public SFile (String s_file) throws NullPointerException, ArrayIndexOutOfBoundsException, InvalidInputException
    {
        try
        {
            FileInputValidation.validateObject(s_file); // O(n²/2)

            Scanner scan = new Scanner(s_file);
            StringBuilder sb = new StringBuilder();
            sb.append(scan.nextLine());

            this.N = Integer.parseInt(sb.toString());
            if(this.N <= 0) throw new NullPointerException();

            this.M = new int[this.N];
            this.S_toName = new ArrayList<>();
            this.S = new ArrayList<>();

            int i = 0;
            while(scan.hasNext())
            {
                // ------- M scan -------
                sb.delete(0, sb.length());
                sb.append(scan.nextLine());                                 // Reading of M

                this.M[i] = Integer.parseInt(sb.toString());

                // ------- S scan -------

                sb.delete(0, sb.length());
                sb.append(scan.nextLine());
                String temp1 = sb.toString();                                // Scan of s[i] in one String

                String[] temp2 = temp1.split(" "); // O(n)             // Split temp 2 in one String[]
                this.S.add(temp2);                                           // add ArrayString (elements of s[i]) to SFile
                if(temp2.length != this.M[i]) throw new ArrayIndexOutOfBoundsException();

                Name[] temp3 = Name.createArrayName(temp2); // O(n)
                this.S_toName.add(temp3);                                    // add ArrayName <String, int, int> to SFile
                i++;
            }
        }
        catch (InvalidInputException | ArrayIndexOutOfBoundsException | NullPointerException e)
        {
            throw e;
        }
    }

    /** ---- GETTERS ---- */

    // @ ensures   \result <==> this.N;
    // @ pure
   /*+INFERRED@
     @ public normal_behavior
     @     ensures \result == this.N; 
     @     ensures `terminationPosition == 5587; 
     @     ensures `exception == null; 
     @*/
    public int getN() {
        return this.N;
    }


    // @ ensures   \result <==> this.M;
    // @ pure
   /*+INFERRED@
     @ public normal_behavior
     @     ensures \result == this.M; 
     @     ensures `terminationPosition == 5698; 
     @     ensures `exception == null; 
     @*/
    public int[] getM() {
        return this.M;
    }

    // @ ensures   \result <==> this.NS_toName;
    // @ pure
   /*+INFERRED@
     @ public normal_behavior
     @     ensures \result == this.S_toName; 
     @     ensures `terminationPosition == 5835; 
     @     ensures `exception == null; 
     @*/
    public ArrayList<Name[]> getS_toName() {
        return this.S_toName;
    }

    // @ ensures   \result <==> this.getS_toName().get(index);
    // @ pure
    public Name[] getS_toName_atIndex(int index)
    {
        return this.getS_toName().get(index);
    }

    // @ ensures   \result <==> this.S;
    // @ pure
   /*+INFERRED@
     @ public normal_behavior
     @     ensures \result == this.S;
     @     ensures `terminationPosition == 6151;
     @     ensures `exception == null;
     @*/
    public ArrayList<String[]> getS() {
        return this.S;
    }

}
