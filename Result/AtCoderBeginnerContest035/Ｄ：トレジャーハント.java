import java.util.*;
 
public class Main {
	public static void main(String[] args) {
		Scanner sc = new Scanner(System.in);
 
		int N = sc.nextInt();
		int M = sc.nextInt();
		long T = sc.nextInt();
 
		Town[] towns = new Town[N];
		for (int i = 0; i < N; i++) {
			towns[i] = new Town(sc.nextInt(), i);
		}
 
		for (int i = 0; i < M; i++) {
			Road r = new Road();
			towns[sc.nextInt() - 1].roads.add(r);
			r.to = sc.nextInt() - 1;
			r.cost = sc.nextInt();
		}
 
 
		Queue<State> states = new LinkedList<>();
		states.add(new State(towns[0], 0, 0, towns[0].money));
 
		ArrayList<State> goals = new ArrayList<>();
 
		while (true) {
			State s = states.poll();
 
			if (s == null) {
				break;
			}
 
			if (s.time > T) {
				continue;
			}
 
			if (s.pos.index == 0) {
				goals.add(s);
			}
 
			int m = s.maxmoney;
			if (m < s.pos.money) {
				m = s.pos.money;
			}
 
			for (Road r : s.pos.roads) {
				states.offer(new State(towns[r.to], s.money, s.time + r.cost, m));
			}
		}
 
		int max = -1;
 
		for (int i = 0; i < goals.size(); i++) {
			State g = goals.get(i);
			if (g.time < T) {
				g.money += g.maxmoney * (T - g.time);
			}
 
			if (max < g.money) {
				max = g.money;
			}
		}
 
		System.out.println(max);
	}
}
 
class State {
	Town pos;
	int money;
	int time;
 
	int maxmoney;
 
	public State(Town pos, int money, int time, int maxmoney) {
		this.pos = pos;
		this.money = money;
		this.time = time;
		this.maxmoney = maxmoney;
	}
}
 
class Town {
	int index;
	int money;
 
	ArrayList<Road> roads;
 
	public Town(int money, int index) {
		this.money = money;
		this.index = index;
		roads = new ArrayList<>();
	}
}
 
class Road {
	int to;
	int cost;
}