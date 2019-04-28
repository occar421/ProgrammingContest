import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		String s = sc.next();
		String[] s_a = s.split("\\+");

		int counter = 0;
		for (int i = 0; i < s_a.length; i++) {
			char[] arr = s_a[i].toCharArray();
			boolean flag = true;
			for (int j = 0; j < arr.length; j++) {
				if (arr[j] == '0') {
					flag = false;
				}
			}
			if (flag) {
				counter++;
			}
		}
		System.out.println(counter);
	}
}