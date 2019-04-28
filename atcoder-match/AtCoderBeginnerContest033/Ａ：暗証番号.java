import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		int num = sc.nextInt();

		int[] a = new int[4];
		a[0] = num / 1000 % 10;
		a[1] = num / 100 % 10;
		a[2] = num / 10 % 10;
		a[3] = num % 10;

		for (int i = 1; i < a.length; i++) {
			if (a[0] != a[i]) {
				System.out.println("DIFFERENT");
				return;
			}
		}
		System.out.println("SAME");
	}
}