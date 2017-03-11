import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		int size = sc.nextInt();

		String[] n_a = new String[size];
		long[] p_a = new long[size];

		long sum = 0;
		for (int i = 0; i < size; i++) {
			n_a[i] = sc.next();
			sum += (p_a[i] = sc.nextLong());
		}

		for (int i = 0; i < size; i++) {
			if (p_a[i] > sum / 2) {
				System.out.println(n_a[i]);
				return;
			}
		}
		System.out.println("atcoder");
	}
}