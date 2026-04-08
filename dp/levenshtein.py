def damerau_levenshtein(s1: str, s2: str) -> int:
    len1, len2 = len(s1), len(s2)

    dp = [[0] * (len2 + 1) for _ in range(len1 + 1)]

    for i in range(len1 + 1):
        dp[i][0] = i
    for j in range(len2 + 1):
        dp[0][j] = j

    for i in range(1, len1 + 1):
        for j in range(1, len2 + 1):
            cost = 0 if s1[i - 1] == s2[j - 1] else 1

            dp[i][j] = min(
                dp[i - 1][j] + 1,       # удаление
                dp[i][j - 1] + 1,       # вставка
                dp[i - 1][j - 1] + cost # замена (или совпадение)
            )

            # перестановка соседних символов
            if i > 1 and j > 1 and s1[i - 1] == s2[j - 2] and s1[i - 2] == s2[j - 1]:
                dp[i][j] = min(dp[i][j], dp[i - 2][j - 2] + cost)

    return dp[len1][len2]