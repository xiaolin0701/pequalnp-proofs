GATES = [('or', 13, 23), ('or', 26, 17), ('or', 15, 14), ('or', 28, 19), ('and', 0, 27), ('or', 30, 25), ('and', 31, 0), ('or', 31, 29), ('or', 32, 2), ('and', 34, 33), ('or', 14, 13), ('or', 36, 24), ('or', 37, 18), ('and', 1, 38), ('or', 16, 15), ('or', 40, 13), ('or', 41, 20), ('and', 3, 42), ('or', 17, 16), ('or', 44, 14), ('or', 45, 21), ('and', 4, 46), ('or', 18, 17), ('or', 48, 15), ('or', 49, 22), ('and', 5, 50), ('or', 19, 18), ('or', 52, 16), ('or', 53, 23), ('and', 6, 54), ('or', 20, 19), ('or', 56, 17), ('or', 57, 24), ('and', 7, 58), ('or', 21, 20), ('or', 60, 18), ('or', 61, 25), ('and', 8, 62), ('or', 22, 21), ('or', 64, 19), ('or', 65, 13), ('and', 9, 66), ('or', 23, 22), ('or', 68, 20), ('or', 69, 14), ('and', 10, 70), ('or', 24, 23), ('or', 72, 21), ('or', 73, 15), ('and', 11, 74), ('or', 25, 24), ('or', 76, 22), ('or', 77, 16), ('and', 12, 78), ('or', 35, 39), ('or', 80, 43), ('or', 81, 47), ('or', 82, 51), ('or', 83, 55), ('or', 84, 59), ('or', 85, 63), ('or', 86, 67), ('or', 87, 71), ('or', 88, 75), ('or', 89, 79)]
def simulate(x, y):
    wires = [bool(x >> i & 1) for i in range(13)] + [bool(y >> i & 1) for i in range(13)]
    for op,a,b in GATES:
        assert a != b and a < len(wires) and b < len(wires)
        wires.append((wires[a] and wires[b]) if op == 'and' else (wires[a] or wires[b]))
    return wires
lines = [sum(1 << ((j+d)%13) for d in (0,1,3,9)) for j in range(13)]
accepts = rejects = maximal = 0
for j,points in enumerate(lines):
    for i in range(13):
        if points >> i & 1:
            assert simulate(1<<i, 1<<j)[-1]
            accepts+=1
for x in range(8192):
    y=sum(1<<j for j,b in enumerate(lines) if x&b==0)
    assert not simulate(x,y)[-1]
    rejects+=1
    maxim=sum(1<<p for p in range(13) if not any((y>>j&1) and (b>>p&1) for j,b in enumerate(lines)))
    maximal+=int(maxim==x)
for i in (0,13):
    bs=simulate(0,1) if i==0 else simulate(1,0)
    d=[j==i for j in range(26)]
    for op,a,b in GATES:
        d.append(((d[a] and bs[b]) or (d[b] and bs[a])) if op=='and' else d[a] or d[b])
    assert not d[-1]
print(len(GATES),accepts,rejects,maximal,"both read flags false")
