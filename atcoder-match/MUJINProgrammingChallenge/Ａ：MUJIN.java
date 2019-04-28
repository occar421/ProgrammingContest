import java.util.*;

public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);

		String l = sc.next();
		char c = l.toCharArray()[0];

		switch (c) {
			case 'O':
			case 'P':
			case 'K':
			case 'L':
				System.out.println("Right");
				break;
			default:
				System.out.println("Left");
		}
	}
}