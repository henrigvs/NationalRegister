package org;
import org.Problem1.SolutionNaive;

public class Main
{
    public static String[] problem_1_naive(String s_file){
        /*System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        String[] s_tmp = {"Peeters", "Goossens", null, "Leclercq"};
        */
        return SolutionNaive.Naive(s_file);
    }

    public static String[] problem_1(String s_file) {
        /*
        System.out.println("===");
        System.out.println(s_file);
        System.out.println("===");
        String[] s_tmp = {"Peeters", "Goossens", null, "Leclercq"};
        */
        return Problem1.SolutionDivideAndConquer.DivideAndConquer(s_file);
    }
}
