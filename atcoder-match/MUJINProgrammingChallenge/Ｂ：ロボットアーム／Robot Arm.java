import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		int oa = sc.nextInt();
		int ab = sc.nextInt();
		int bc = sc.nextInt();

		double R = oa + ab + bc;
		double S = Math.PI * R * R;

		double r = 0;
		if (oa > ab + bc) {
			r = oa - (ab + bc);
		} else if (ab > oa + bc) {
			r = ab - (oa + bc);
		} else if (bc > oa + ab) {
			r = bc - (oa + ab);
		}
		double s = Math.PI * r * r;

		System.out.println(S - s);
	}
}