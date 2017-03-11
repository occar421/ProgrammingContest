import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		int size = sc.nextInt();
		int[] x_a = new int[size];
		int[] y_a = new int[size];

		for (int i = 0; i < size; i++) {
			x_a[i] = sc.nextInt();
			y_a[i] = sc.nextInt();
		}

		int ei_t = 0;
		int ch_t = 0;
		int do_t = 0;

		for (int i = 0; i < size; i++) {
			for (int j = i + 1; j < size; j++) {
				for (int k = j + 1; k < size; k++) {
					int a_x = x_a[i];
					int a_y = y_a[i];
					int b_x = x_a[j];
					int b_y = y_a[j];
					int c_x = x_a[k];
					int c_y = y_a[k];

					int cos_a_ = dot(a_x, a_y, b_x, b_y, c_x, c_y);
					int cos_b_ = dot(b_x, b_y, a_x, a_y, c_x, c_y);
					int cos_c_ = dot(c_x, c_y, a_x, a_y, b_x, b_y);

					if (cos_a_ == 0 || cos_b_ == 0 || cos_c_ == 0) {
						ch_t++;
					} else if (cos_a_ < 0 || cos_b_ < 0 || cos_c_ < 0) {
						do_t++;
					} else {
						ei_t++;
					}
				}
			}
		}

		System.out.println("" + ei_t + " " + ch_t + " " + do_t);
	}

	static int dot(int base_x, int base_y, int ax, int ay, int bx, int by) {
		int aax = ax - base_x;
		int aay = ay - base_y;
		int bbx = bx - base_x;
		int bby = by - base_y;
		return aax * bbx + aay * bby;
	}
}