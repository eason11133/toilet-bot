n = int(input())
scores = list(map(int,input().split()))
scores.sort()
print(" ".join(map(str,scores)))
pass_scores = [x for x in scores if x>=60]
fail_scores = [x for x in scores if x<60]
if fail_scores:
    print(max(fail_scores))
else:
    print('best case')
if pass_scores:
    print(min(pass_scores))
else:
    print('worst case')