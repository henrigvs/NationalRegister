/*
    Created, specified and implemented by Henri GEVENOIS
    As part of the course of algorithmics II at University of Namur
 */

package Problem1.DataInit;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FileInputValidation
{
    /*
        @           public normal_behavior
        @ requires  s_file != null;
        @ ensures   (InvalidInputException e) == false;
        @
        @           public exceptional_behavior
        @ signals   (InvalidInputException e) == true;
     */

    /**
     * complexity => O(n²/2) | Since inner loop is browsed only n/2 times
     */
    public static void validateObject(String s_file) throws InvalidInputException
    {
        try
        {
            Pattern INT_REGEX = Pattern.compile("(^[0-9]+$)");
            Pattern NAMES_SEQUENCE_REGEX = Pattern.compile("^[A-Za-zÁ-Ú]+ ?");

            if (s_file == null)
                throw new InvalidInputException("Invalid Input Exception : s_file == null");
            Scanner scan = new Scanner(s_file);
            if (!scan.hasNext())
                throw new InvalidInputException("Invalid Input Exception : s_file is empty");

            StringBuilder sb = new StringBuilder();
            sb.append(scan.nextLine());
            int n = Integer.parseInt(sb.toString());
            Matcher nMatcher = INT_REGEX.matcher(sb.toString());
            if (!nMatcher.matches())
                throw new InvalidInputException("Invalid Input Exception : N");

            int i = 1;
            int m;
            String[] s;
        /*
            @ loop_invariant    n <==> \old(n);
            @ loop_invariant    0 < i && i <= n;
            @ maintaining       \index >= 0 && \index <= array.length;
            @ decrease          scan.length - \index;
         */
            while (scan.hasNext()) {
                sb.delete(0, sb.length());
                sb.append(scan.nextLine());
                Matcher mMatcher = INT_REGEX.matcher(sb.toString());
                if (!mMatcher.matches())
                    throw new InvalidInputException("Invalid Input Exception : M" + i);
                m = Integer.parseInt(sb.toString());

                sb.delete(0, sb.length());
                sb.append(scan.nextLine());

                s = sb.toString().split(" ");
                for (String name : s) {
                    Matcher sMatcher = NAMES_SEQUENCE_REGEX.matcher(name);
                    if (sMatcher.matches() == false)
                        throw new InvalidInputException("Invalid Input Exception : S" + i);
                }

                if (s.length != m)
                    throw new InvalidInputException("Invalid Input Exception #S" + i + " != #M" + i);
                if (i < Integer.MAX_VALUE)
                    i++;
            }
            if (i > Integer.MIN_VALUE)
                i = i - 1;
            if (n != i)
                throw new InvalidInputException("Invalid Input Exception #M != N");
        }
        catch (InvalidInputException e)
        {
            throw e;
        }
    }
}
