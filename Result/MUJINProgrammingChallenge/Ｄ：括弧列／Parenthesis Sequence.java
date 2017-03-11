import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		int N = sc.nextInt();
		String S = sc.next();
		int Q = sc.nextInt();

		for (int i = 0; i < Q; i++) {
			int l = sc.nextInt();
			int r = sc.nextInt();

			if ((r - l) % 2 == 0) {
				System.out.println("No");
				continue;
			}

			ArrayList<Integer> list = new ArrayList<>();
			list.add(0);

			boolean flag = false;
			for (int j = l - 1; j < r; j++) {
				int size = list.size();
				switch (S.charAt(j)) {
					case '(':
						for (int k = 0; k < size; k++) {
							list.set(k, list.get(k) + 1);
						}
						break;
					case ')':
						int r_n = 0;
						for (int k = 0; k < size; k++) {
							int val = list.get(k - r_n) - 1;
							if (val < 0) {
								list.remove(k - r_n);
								r_n++;
							} else {
								list.set(k - r_n, val);
							}
						}
						break;
					case '?':
						if (j == l - 1) {
							list.set(0, list.get(0) + 1);
						} else {
							for (int k = 0; k < size; k++) {
								list.add(list.get(k) + 1);
								list.set(k, list.get(k) - 1);
							}
						}
						break;
				}
			}
			for (int j = 0; j < list.size(); j++) {
				if (list.get(j) == 0) {
					flag = true;
				}
			}
			System.out.println(flag ? "Yes" : "No");
		}
	}
}