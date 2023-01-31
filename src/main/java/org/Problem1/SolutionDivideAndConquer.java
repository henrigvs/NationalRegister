/*
    Created, specified and implemented by Henri GEVENOIS
    As part of the course of algorithmics II at University of Namur
 */
package Problem1;

import Problem1.DataInit.InvalidInputException;
import Problem1.DataInit.Name;
import Problem1.DataInit.SFile;

import java.util.*;

public class SolutionDivideAndConquer
{
    /*
        @               public normal_behavior
        @ requires      (* n ∈ s_file : 0 < n < Integer.MAX_VALUE);
        @ requires      (* n == #S == #M);
        @ requires      (* M ∈ s_file : (\typeof(M) == \elemtype(int[]) && M != null && \for all int i; 0 <= i < n; 0 < M[i] < Integer.MAX_VALUE *);
        @ requires      (* S ∈ s_file : (\typeof(S) == \elemtype(String[][]) && S != null && \for all int i; 0 <= i < n; (\for all j; 0 <= j < M[i]; S[i][j] != null *);
        @ requires      (InvalidObjectException e) false (* new FileInputValidation(s_file).validateObject() has to pass *);
        @
        @ ensures       s_file <==> \old(s_file);
        @ ensures       Solution.length == SFILE.getN();
        @ ensures       \for all int i; 0 <= i && i < SFILE.getN();
        @                   (\for all int j; 0 <= j && j < SFILE.getM()[i];
        @                       (\exists int k; 0 <= k && k < SFILE.getM()[i];
        @                           && (\num_of int l; 0 <= l && l < SFILE.getM()[i]; SFILE.getS_atIndex(i)[l].equals(SFILE.getS_atIndex(i)[k])) > SFILE.getM()[i] / 2)))
        @                               ==> (\result[i] == SFILE.getS_atIndex(i)[k]))
        @                   &&  (\for all int k; 0 <= k && k < SFILE.getM()[i];
        @                           && (\num_of int l; 0 <= l && l < SFILE.getM()[i]; (SFILE.getS_atIndex(i)[l].equals(SFILE.getS_atIndex(i)[k])) <= SFILE.getM()[i] / 2)))
        @                               ==> (\result[i] == null));
        @
        @ also          public exceptional_behavior
        @ requires      s_file == null;
        @ ensures       \result <==> null;
        @ signals_only  NullPointerException, ArrayIndexOutOfBoundsException, InvalidObjectException;
        @ signals       (InvalidObjectException e) true;
        @ pure
     */

    /**
     * Complexity => O(n² log n)
     */
    public static /*@ nullable */ String[] DivideAndConquer(String s_file)
    {
        String[] Solution = new String[0];              // O(1)
        try
        {
            SFile SFILE = new SFile(s_file);            // O(n²/2)
            Solution = new String[SFILE.getN()];        // O(1)
            /*
                @ loop_invariant        0 <= i && i < SFILE.getN();
                @ loop_invariant        \for all int j; 0 <= j && j < i; Solution[j] == pickTheBest(SFILE.getS_toName_atIndex(j));
                @ decrease              SFILE.getN() - i;
            */
            for (int i = 0; i < SFILE.getN(); i++)      // O(n)
            {
                Solution[i] = pickTheBest(SFILE.getS_toName_atIndex(i), SFILE.getM()[i]);   // O(n log n);
            }
        }
        catch (NullPointerException | ArrayIndexOutOfBoundsException | InvalidInputException e)
        {
            return null;
        }
        return Solution;
    }

    /*
        @               public normal_behavior
        @ requires      m == MyTest.length;
        @ requires      0 < m && m < Integer.MAX_VALUE - 1;
        @ requires      MyTest != null && \for int i; 0 <= i && i < m; MyTest[i] != null;
        @ assignable	\for all int i; 0 <= i < m; MyTest[i].getHashCode() && MyTest[i].getNbOccurences();
        @
        @ ensures       \for all int i; 0 <= i < m; MyTest[i].getName() == \old(MyTest[i].getName());
        @ ensures		m <==> \old(m);
        @ ensures       \for all int i; 0 <= i && i < m; MyTest[i].getHashCode() == 0 && MyTest[i].getOccurence() == 0;
        @
        @ ensures       \result <==> names.getName()[j] ==>   
        @									(\for all int i; 0 <= i && i < m;
        @                               		(\exists int j; 0 <= j && j < m;
        @                          					(\num_of int k; 0 <= k && k < m; names[j][k].getName().equals(names[i][k].getName())) > ((double) m) / 2));
        @ ensures       \result <==> null ==>       
        @									(\for all int i; 0 <= i && i < m;
        @                                   	(\for all int j; 0 <= j && j < m;
        @                                       	(\num_of int k; 0 <= k && k < m; names[j][k].getName().equals(names[i][k].getName())) <= ((double) m) / 2));
        @				
        @				public exceptional_behavior
        @ requires		MyTest == null || m <= 0;
        @ requires      m > Integer.MAX_VALUE - 1;
        @ assignable	\nothing;
        @ signals		(ArithmeticException | ArrayIndexOutOfBoundsException | NullPointerException e) true;
    */

    /**
     *      Complexity algo => 0(3n log n) = O(n log n)
     */
    public static /*@ nullable */ String pickTheBest(Name[] MyTest, int m)
    {
        try
        {
            if(m < Integer.MIN_VALUE + 1)
            	throw new ArithmeticException();
        	int start = 0;
            int end = m - 1;
            HashMap<Integer, Integer> SolutionTab = new HashMap<Integer, Integer>(); SolutionTab.put(0, 0);
            String result = new String();

            if(m == 1)
            {
                return new String(MyTest[0].getName());
            }
            else
            {
                Divide(MyTest, start, end, SolutionTab);        //O(n log n)

                int ValueOccurenceMAX = SolutionTab.get(0);
                if(ValueOccurenceMAX <= ((double) m) / 2)
                    return null;
                else
                {
                    int HashCodeMAX = 0;
                    Iterator<Map.Entry<Integer, Integer>> it = SolutionTab.entrySet().iterator();

                /*
                    @ loop_invariant        (key == 0 && \fresh(value) != ValueOccurenceMAX) ==> HashCodeMAX == 0
                    @                   &&  (key != 0 && \fresh(value) == ValueOccurenceMAX) ==> HashCodeMAX == key;
                    @ loop_invariant    \index >= 0 && \index <= array.length;
                    @ maintaining       \invariant_for(Iterator);
                    @ decrease          SolutionTab.size() - \index;
                    @ assignable        HashCodeMAX;
                 */
                    while (it.hasNext())                        // O(n);
                    {
                        Map.Entry pair = (Map.Entry) it.next();
                        int key = Integer.parseInt(pair.getKey().toString());
                        int value = Integer.parseInt(pair.getValue().toString());
                        if(key != 0 && value == ValueOccurenceMAX )
                        {
                            HashCodeMAX = key;
                            break;
                        }
                        it.remove();
                    }

                /*
                    @ loop_invariant    Name.length <==> old(Name.length);
                    @ loop_invariant    \index >= 0 && \index <= array.length;
                    @ loop_invariant        name.getName().hashCode() == HashCodeMAX ==> result == new String(name.getName()
                    @                   &&  name.getName().hashCode() != HashCodeMAX ==> result == \old(result);
                    @ decrease          Name.length - \index;
                    @ assignable        result;
                 */
                    for (Name name : MyTest)                    // O(n)
                    {
                        if(name.getName().hashCode() == HashCodeMAX) {
                            result = new String(name.getName());
                            break;
                        }
                    }
                }
                return result;
            }
        }
        catch (ArithmeticException | NullPointerException | ArrayIndexOutOfBoundsException e)
        {
            throw e;
        }
    }

    /*
        @ requires      0 < MyTest.length && MyTest.length < Integer.MAX_VALUE;
        @ requires      0 <= start && fin <= MyTest.length;
        @ requires      (start + end) / 2 > Integer.MIN_VALUE && (start + end) / 2 < Integer.MAX_VALUE;
        @ requires      MyTest != null && \for int i; 0 <= i && i < m; MyTest[i] != null;
        @ requires      SolutionTab.size() == 1 && SolutionTab.get(0) == 0;
        @
        @ assignable    SolutionTab;
        @
        @ ensures       \for all Integer key; SolutionTab.keySet();
        @                               key.intValue() != 0 ==> SolutionTab.get(key) == (\num int j; 0 <= j && j < MyTest.length; MyTest[J].getHashCode().equals(key.intValue())
        @                           &&  key.intValue() == 0 ==> SolutionTab.get(key) == (\max Integer x; SolutionTab.keySet(); x.intValue());
        @               (*
        @                   for any key of type Integer, in the set of key of SolutionTab,
        @                                       if key != 0, then the value at SolutionTab.get(key) == the number of hashcode (== key) present in MyTest
        @                                       if key == 0, then the value at SolutionTab.get(key) == the number of highest value in SolutionTab (Occurence Max)
        @               *)
        @
        @ ensures       end - start > 1 ==> MyTest == \old(MyTest)
        @           &&  end - start == 1 ==> (\for all int i; 0 <= i && i < MyTest.length; MyTest[i].getHashCode == 0 && MyTest[i].getNbOccurences == 0);
    */
    /**
     *  Complexity => O(n log n)
     */
    public static void Divide(Name[] MyTest, int start, int end, HashMap<Integer, Integer> SolutionTab)
    {
    	try {
            // find the middle point
    		if(start < 0 || end < 0)
    			throw new ArithmeticException();
            int mid = start + (end - start)/2;
            if (start < end)
            {



                // Divide MyTest in unique element
                /*
                 * @assert 0 < start && start < Integer.MAX_VALUE/2;
                 * @assert 0 < mid && mid < Integer.MAX_VALUE/2;
                 * @assert 0 < end && end < Integer.MAX_VALUE/2;
                 */
                Divide(MyTest, start, mid, SolutionTab);             // O(log n)
                Divide(MyTest, mid + 1, end, SolutionTab);      // O(log n)

                // Each element will work alone to mention itself in HashMap
                Conquer(MyTest, start, mid, end, SolutionTab);      // O(n)
            }
        }
        catch (ArithmeticException e)
        {
            throw e;
        }
    }


    /*
        @ requires      MyTest != null && (\for all int i; 0 <= i && i < MyTest.length; MyTest[i] != null;
        @ requires		MyTest.length > 0 && MyTest.length < Integer.MAX_VALUE;
        @
        @ ensures       for all int i; 0 <= i && i < MyTest.length; MyTest[i].getHashCode() == 0 && MyTest[i].getOccurence() == 0;
        @ ensures       \for all Integer key; SolutionTab.keySet();
        @                       key.intValue() != 0 ==> SolutionTab.get(key) == (\num int j; 0 <= j && j < MyTest.length; MyTest[J].getHashCode().equals(key.intValue())
        @                   &&  key.intValue() == 0 ==> SolutionTab.get(key) == (\max Integer x; SolutionTab.keySet(); x.intValue());
        @ code_java_math
    */

    /**
     * Complexity => O(n) => 2 successive loops on a total of (end - start) length
     */
    public static void Conquer(Name[] MyTest, int start, int mid, int end, HashMap<Integer, Integer> SolutionTab)
    {
        try
        {
        	if(mid < 0 || start < 0 || end < 0 || (mid - start) > Integer.MAX_VALUE - 1)
        		throw new ArithmeticException();
        	int sizeLeftPart = (mid - start) +1;
            int sizeRightPart = end - mid;
            
            Name[] LeftPart = new Name[sizeLeftPart];
            Name[] RightPart = new Name[sizeRightPart];

            for (int i = 0; i < sizeLeftPart; i++)
            {
                LeftPart[i] = MyTest[start + i];
            }
            for (int i = 0; i < sizeRightPart; i++)
            {
                RightPart[i] = MyTest[mid + 1 + i];
            }

            GenerateHashMapForValuesOccurences(LeftPart, SolutionTab);      // O(1)
            GenerateHashMapForValuesOccurences(RightPart, SolutionTab);     // O(1)
        }
        catch (ArithmeticException | NullPointerException | ArrayIndexOutOfBoundsException e)
        {
            throw e;
        }
    }

    /*
        @ requires      MyTest != null && MyTest.length == 1;
        @ requires      SolutionTab.isEmpty() == false;
        @ requires		\for all Integer Value; SolutionTab.values(); Integer.MIN_VALUE < Value && Value < Integer.MAX_VALUE;
        @
        @ ensures       (!SolutionTab.containsKey(key) && SolutionTab.containsKey(key) != 0)
        @                           ==>  (
        @                                    SolutionTab.put(key, value)
        @                                 && MyTest[0].getNbOccurences() == 0
        @                                 && MyTest[0].getHashCode() == 0
        @                                 && SolutionTab.get(key) > SolutionTab.get(0) ==> SolutionTab.get(0) == SolutionTab.get(key);
        @                                ))
        @           &&  (SolutionTab.containsKey(MyTest[0].getHashCode() && SolutionTab.containsKey(MyTest[0].getHashCode() != 0)
        @                           ==>  (
        @                                    SolutionTab.replace(MyTest[0].getHashCode(), MyTest[0].getNbOccurences(), MyTest[0].getNbOccurences() + 1)
        @                                 && MyTest[0].getNbOccurences() == 0
        @                                 && MyTest[0].getHashCode() == 0
        @                                 && SolutionTab.get(key) > SolutionTab.get(0) ==> SolutionTab.get(0) == SolutionTab.get(key);
        @                                ));
        @
        @ ensures       MyTest[0].getHashCode() == 0;
        @ ensures       MyTest[0].getNbOccurences() == 0;
     */

    /**
     *  Complexity => O(1), since each operation is just an affectation or a test on HashMap with O(1) complexity;
     */
    public static /* @code_safe_math */ void GenerateHashMapForValuesOccurences(Name[] MyTest, HashMap<Integer, Integer> SolutionTab)
    {
        try {
            int key = MyTest[0].getHashCode();
            int value = MyTest[0].getNbOccurences();
            if(key != 0)
            {
                if (!SolutionTab.containsKey(key))
                {
                    SolutionTab.put(key, value);
                    MyTest[0].setNbOccurences(0);
                    MyTest[0].setHashCode(0);
                    if(SolutionTab.get(key) > SolutionTab.get(0))
                        SolutionTab.replace(0, SolutionTab.get(0), SolutionTab.get(key));
                }
                else if (SolutionTab.containsKey(key))
                {
                    value = SolutionTab.get(key);
                    if(SolutionTab.get(key) < Integer.MAX_VALUE - 1)
                    	SolutionTab.replace(key, value, value + 1);
                    MyTest[0].setNbOccurences(0);
                    MyTest[0].setHashCode(0);
                    if(SolutionTab.get(key) > SolutionTab.get(0))
                        SolutionTab.replace(0, SolutionTab.get(0), SolutionTab.get(key));
                }
            }
        }
        catch (ArrayIndexOutOfBoundsException | NullPointerException e)
        {
            throw e;
        }
    }
}
