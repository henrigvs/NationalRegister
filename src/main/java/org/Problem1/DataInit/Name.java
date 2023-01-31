/*
    Created, specified and implemented by Henri GEVENOIS
    As part of the course of algorithmics II at University of Namur
 */
package Problem1.DataInit;

public class Name
{
    private /* @spec_public */ String Name;
    private /* @spec_public */ int HashCode;
    private /* @spec_public */ int NbOccurences;

    /*
        @ public invariant      sNameSN != null;
        @ public invariant      Integer.MIN_VALUE > HashCode && HashCode < Integer.MAX_VALUE;
        @ public invariant      0 <= NbOccurences && NbOccurences < Integer.MAX_VALUE;
     */


    /** ---- CONSTRUCTORS ---- */

    /*
        @ requires              name != null;
        @ assignable            \everything;
        @ ensures               this.Name.equals(name);
        @ ensures               this.HashCode == name.hashCode();
        @ ensures               this.NbOccurences = 1;
     */

    /**
     * complexity => O(1) | since only operations of affectation
     */
    public Name(String name)
    {
        this.Name = new String(name);
        this.HashCode = name.hashCode();
        this.NbOccurences = 1;
    }

    /** ---- GETTERS ---- */

    /*
      @ ensures       \result <==> this.Name;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures \result == this.Name; 
      @     ensures `terminationPosition == 1247; 
      @     ensures `exception == null;
    */

    /**
     * complexity => O(1) | since only operation of affectation
     */
    public /* @pure */  String getName()
    {
        return this.Name;
    }

    /*
      @ ensures       \result <==> this.HashCode;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures \result == this.HashCode; 
      @     ensures `terminationPosition == 1394; 
      @     ensures `exception == null; 
      @*/
    /**
     * complexity => O(1) | since only operation of affectation
     */
    public /* @pure */ int getHashCode()
    {
        return this.HashCode;
    }

    /*
      @ ensures       \result <==> this.NbOccurences;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures \result == this.NbOccurences; 
      @     ensures `terminationPosition == 1552; 
      @     ensures `exception == null; 
      @*/
    /**
     * complexity => O(1) | since only operations of affectation
     */
    public /* @pure */ int getNbOccurences()
    {
        return this.NbOccurences;
    }

    /** ---- SETTERS ---- */

    /*
      @ requires      name != null;
      @ ensures       this.Name = name;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures this.Name == name; 
      @     assignable this.Name; 
      @     
      @*/
    /**
     * complexity => O(1) | since only operations of affectation
     */
    public void setName(String name)
    {
        this.Name = name;
    }

    /*
      @ requires      0 <= hashCode && hashCode < Integer.MAX_VALUE;
      @ ensures       this.HashCode = hashCode;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures this.HashCode == hashCode; 
      @     assignable this.HashCode; 
      @
    */
    /**
     * complexity => O(1) | since only operations of affectation
     */
    public void setHashCode(int hashCode)
    {
        this.HashCode = hashCode;
    }

    /*
      @ requires      0 <= nb_occurences && nb_occurences < Integer.MAX_VALUE;
      @ ensures       this.NbOccurences = nb_occurences;
      @ public normal_behavior
      @     requires this.Name != null; 
      @     ensures this.NbOccurences == nb_occurences; 
      @     assignable this.NbOccurences; 
      @
    */
    /**
     * complexity => O(1) | since only operations of affectation
     */
    public void setNbOccurences(int nb_occurences)
    {
        this.NbOccurences/**
         * complexity => O(1) | since only operations of affectation
         */ = nb_occurences;
    }


    /** ---- Methods inheriting of Name ---- */

    /*
        @ requires      s != null && (\for all int i; 0 <= i && i < s.length; s[i] != null;
        @ ensures       \result <==> \for all int j; 0 <= j && j < s.length; result[i] = new Name(s[i]);
     */
    /**
     * complexity => O(n) | since a loop is browsed s.length times
     */
    public static Name[] createArrayName(String [] s) throws NullPointerException, ArrayIndexOutOfBoundsException
    {
        try
        {
            int size = s.length;

            for (int i = 0; i < size; i++)
            {
                if(s[i] == null)
                    throw new NullPointerException();
            }
            // @ assert     s != null && s.length > 0;
            // @ assert     \for all int i; 0 <= i && i < size; s[i] != null;

            Name[] result = new Name[size];

            for (int i = 0; i < size; i++)
            {
                if(s[i] != null)
                    result[i] = new Name(s[i]);
            }
            return result;
        }
        catch (NullPointerException | ArrayIndexOutOfBoundsException e)
        {
            throw e;
        }
    }
}
