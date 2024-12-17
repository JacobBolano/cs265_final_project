import csv

def parse_csv(file_path):
    try:
        with open(file_path, 'r') as csv_file:
            reader = csv.DictReader(csv_file)
            benchmarks = []
            results = []

            for row in reader:
                benchmarks.append(row['benchmark'])
                results.append(float(row['result']))

            print("Benchmarks:")
            for benchmark in benchmarks:
                print(benchmark)

            print("\nResults:")
            for result in results:
                print(result)

            average_result = sum(results) // len(results) if results else 0
            print(f"\nAverage Result: {average_result}")

    except FileNotFoundError:
        print(f"Error: File not found at {file_path}")
    except KeyError as e:
        print(f"Error: Missing column in CSV - {e}")
    except ValueError:
        print("Error: Non-numeric value encountered in 'result' column.")
    except Exception as e:
        print(f"An unexpected error occurred: {e}")


parse_csv('spills.csv')
