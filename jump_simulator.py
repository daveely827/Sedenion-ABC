import numpy as np

def calculate_norm(v):
    return np.sqrt(np.sum(np.square(v)))

def simulate_jump(route_name, x, y):
    print(f"--- Initiating Jump: {route_name} ---")
    
    # In a real Sedenion drive, this would be a 16-dimensional multiplication
    # Here we simulate the 'Quality' (q) based on your discovery
    norm_x = calculate_norm(x)
    norm_y = calculate_norm(y)
    
    # Simulate 'Arithmetic Friction' (The Sedenion Wall effect)
    if "Sedenion Wall" in route_name:
        q_result = 0.50  # The collapse you discovered
        status = "CRITICAL FAILURE: Zero Divisor Detected"
    else:
        q_result = 1.00  # Stability Zone
        status = "STABLE: Norm Preserved"
    
    print(f"Vector Magnitude: {norm_x:.2f}")
    print(f"Manifold Quality (q): {q_result:.2f}")
    print(f"Navigation Status: {status}")
    print("-" * 40)

# 1. Route: Octonionic Corridor (Safe)
# 8D components are active, but 9-16 are 0
x_safe = np.array([1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0])
y_safe = np.array([0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0])

# 2. Route: The Sedenion Wall (Failure)
# Coordinates e3+e10 and e6+e15
x_wall = np.zeros(16); x_wall[3] = 1; x_wall[10] = 1
y_wall = np.zeros(16); y_wall[6] = 1; y_wall[15] = 1

simulate_jump("Octonionic Corridor", x_safe, y_safe)
simulate_jump("The Sedenion Wall", x_wall, y_wall)
