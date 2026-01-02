import matplotlib.pyplot as plt

# Data from our Sedenion Stress Tests
dimensions = [4, 5, 6, 7, 8, 9]
q_values = [1.6299, 1.2590, 1.1921, 1.1044, 1.0182, 0.9634]
primes = ["Orig (4D)", "17 (5D)", "19 (6D)", "23 (7D)", "29 (8D)", "31 (9D)"]

plt.figure(figsize=(10, 6))
plt.plot(dimensions, q_values, marker='o', linestyle='-', color='#2ca02c', linewidth=2)

# Highlighting the "Sedenion Horizon"
plt.axhline(y=1.0, color='r', linestyle='--', label='Sedenion Horizon (q=1.0)')
plt.fill_between(dimensions, q_values, 1.0, where=([q >= 1.0 for q in q_values]), 
                 color='green', alpha=0.1, label='Rigid Zone')

# Annotations
for i, txt in enumerate(primes):
    plt.annotate(txt, (dimensions[i], q_values[i]), textcoords="offset points", xytext=(0,10), ha='center')

plt.title('ABC Quality Collapse Curve: The Sedenion Friction Gradient')
plt.xlabel('Unique Prime Dimensions')
plt.ylabel('Quality (q)')
plt.grid(True, which='both', linestyle='--', alpha=0.5)
plt.legend()

# Save the plot
plt.savefig('collapse_curve.png')
print("Graph generated: collapse_curve.png")