import org.junit.Test;
import org.junit.Rule;
import org.junit.rules.TemporaryFolder;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

import static org.Main.problem_1;
import static org.Main.problem_1_naive;
import static org.hamcrest.MatcherAssert.assertThat;

public class Algo2Problem1Test {



    private String getFileText(String input) throws IOException {
        return new String(Files.readAllBytes(Paths.get(input)));
    }
    @Rule
    public TemporaryFolder testFolder = new TemporaryFolder(); // Create a temporary folder for outputs deleted after tests


    @Test
    public void test_problem_1() throws Exception
    {
        String input = "src/test/resources/problem1/DiviserPourRegner_2.2.txt";
        long lStartTime = System.nanoTime();

        String[] result = problem_1(getFileText(input));

        long lEndTime = System.nanoTime();
        long output = lEndTime - lStartTime;
        System.out.println("Elapsed time in milliseconds : " + output/1000000);

        String[] s_result = {"Peeters", "Goossens", null, "Leclercq"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2] == null);
        assertThat("Testing value[3]", result[3].equals(s_result[3]));

    }

    @Test
    public void test_problem_1_naive() throws Exception
    {
        String input = "src/test/resources/problem1/DiviserPourRegner_2.2.txt";

        long lStartTime = System.nanoTime();

        String[] result = problem_1_naive(getFileText(input));

        long lEndTime = System.nanoTime();
        long output = lEndTime - lStartTime;
        System.out.println("Elapsed time in milliseconds : " + output/1000000);

        String[] s_result = {"Peeters", "Goossens", null, "Leclercq"};
        assertThat("Testing size array", result.length == 4);
        assertThat("Testing value[0]", result[0].equals(s_result[0]));
        assertThat("Testing value[1]", result[1].equals(s_result[1]));
        assertThat("Testing value[2]", result[2] == null);
        assertThat("Testing value[3]", result[3].equals(s_result[3]));

    }
}
