"""
Tom Helmuth
5/31/24

Round robin curling schedule
Using circle algorithm here: https://en.wikipedia.org/wiki/Round-robin_tournament#Circle_method

Ensures that each team plays every other team twice, that each team
plays the same number of games with red and yellow stones, and that
each team plays on each sheet the same number of times (or as close
as possible).

Works for any number of teams 13 or less. Set the number of teams at NUM_TEAMS.
"""

import random, sys

## Set number of teams here
NUM_TEAMS = 10

## Set filename for where to write the CSV. Overwrites this file
OUTPUT_FILENAME = "schedule.csv"

## Set to True to randomize the weeks of the schedule, or False to not
## Note: without this, all teams have streaks of having the same color, which is likely undesirable
SHUFFLE_WEEKS = True

################################################################################
## Don't change anything below here

## Optionally take a command line argument for number of teams
if len(sys.argv) > 1:
    NUM_TEAMS = int(sys.argv[1])
if len(sys.argv) > 2:
    OUTPUT_FILENAME = sys.argv[2]
ODD = (NUM_TEAMS % 2 == 1)

def get_12():
    a = [[(5, 8), (4, 9), (1, 12), (2, 11), (6, 7), (3, 10)],
            [(12, 10), (5, 6), (4, 7), (2, 9), (11, 1), (3, 8)],
            [(3, 6), (11, 9), (4, 5), (12, 8), (2, 7), (1, 10)],
            [(12, 6), (11, 7), (9, 1), (3, 4), (10, 8), (2, 5)],
            [(2, 3), (1, 8), (10, 6), (11, 5), (12, 4), (9, 7)],
            [(7, 1), (12, 2), (11, 3), (10, 4), (8, 6), (9, 5)],
            [(7, 5), (8, 4), (10, 2), (1, 6), (9, 3), (11, 12)],
            [(10, 11), (7, 3), (8, 2), (9, 12), (5, 1), (6, 4)],
            [(1, 4), (6, 2), (8, 11), (5, 3), (9, 10), (7, 12)],
            [(8, 9), (3, 1), (5, 12), (7, 10), (4, 2), (6, 11)],
            [(4, 11), (5, 10), (6, 9), (7, 8), (3, 12), (1, 2)]]
    
    b = [[(6, 7), (5, 8), (1, 12), (2, 11), (3, 10), (4, 9)],
            [(4, 7), (2, 9), (12, 10), (5, 6), (3, 8), (11, 1)],
            [(4, 5), (2, 7), (3, 6), (11, 9), (1, 10), (12, 8)],
            [(2, 5), (3, 4), (11, 7), (10, 8), (12, 6), (9, 1)],
            [(1, 8), (9, 7), (2, 3), (12, 4), (11, 5), (10, 6)],
            [(11, 3), (10, 4), (9, 5), (8, 6), (7, 1), (12, 2)],
            [(11, 12), (1, 6), (10, 2), (9, 3), (7, 5), (8, 4)],
            [(8, 2), (10, 11), (6, 4), (5, 1), (9, 12), (7, 3)],
            [(9, 10), (8, 11), (1, 4), (7, 12), (6, 2), (5, 3)],
            [(3, 1), (5, 12), (8, 9), (7, 10), (4, 2), (6, 11)],
            [(6, 9), (3, 12), (7, 8), (1, 2), (4, 11), (5, 10)]]

    return random.choice([a, b])

def get_stats(assignments):
    """gathers stats on how often teams play on each sheet"""
    teams = len(assignments[0]) * 2

    stats = [{"player":i, "red":0, "yellow":0, "sheets":[0 for _ in range(len(assignments[0]))]} 
             for i in range(teams + 1)]

    for week in assignments:
        for sheet, (red, yellow) in enumerate(week):
            if red != "BYE" and yellow != "BYE":
                ## Update colors
                stats[red]["red"] += 1
                stats[yellow]["yellow"] += 1

                ## Update sheets
                stats[red]["sheets"][sheet] += 1
                stats[yellow]["sheets"][sheet] += 1

    return stats

def analyze(assignments):
    """assignments is a list of tuples"""
    stats = get_stats(assignments)

    if ODD:
        stats = stats[1:-1]
    else:
        stats = stats[1:]

    print("""\nTeams and how many red/yellow stones they have, as well as how
often they play on each sheet.""")
    for player in stats:
        p, red, yellow = player["player"], player["red"], player["yellow"]
        sheets = player["sheets"]
        if ODD:
            sheets = sheets[:-1]
        print(f"Team {p}: {red} red and {yellow} yellow. Sheets = {sheets}")


def tuple_swap(tup):
    """Swaps elements of a 2-tuple"""
    return (tup[1], tup[0])

def sheets_even(assignments):
    """Returns True if no team plays on a sheet more than 2 times."""
    stats = get_stats(assignments)

    for player in stats:
        sheets = player["sheets"]
        for sheet_count in sheets:
            if sheet_count > 2:
                return False
            
    return True

def shuffle_sheets(assignments):
    for week in assignments:
        random.shuffle(week)

def assign_sheets_CSP_recursive(start_assignments, finished_assignments, rows, cols, row, col):
    """Recursively solves assignments.
    rows and cols are number of each
    row and col is current location to assign"""

    if row == rows:
        return "done"
    
    if col == cols:
        return assign_sheets_CSP_recursive(start_assignments, finished_assignments, rows, cols, row + 1, 0)

    # non base cases here
    for tup in start_assignments[row]:
        # Make sure not already used in this row
        if tup in finished_assignments[row]:
            continue

        finished_assignments[row][col] = tup

        # Check if still have even sheet assignments
        if not sheets_even(finished_assignments):
            continue

        # make recursive calls here
        result = assign_sheets_CSP_recursive(start_assignments, finished_assignments, rows, cols, row, col + 1)
        if result == "done":
            return "done"

    finished_assignments[row][col] = ("BYE", "BYE")
    return


def assign_sheets_CSP(assignments):
    """Uses constraint-satisfaction solving to find a solution with even sheets, i.e.
    no team plays on the same sheet more than 2 times. Backtracks as necessary."""
    rows = len(assignments)
    cols = len(assignments[0])
    assignments_to_fill = [[("BYE", "BYE") for _ in range(cols)] for _ in range(rows)]

    assign_sheets_CSP_recursive(assignments, assignments_to_fill, rows, cols, 0, 0)

    return assignments_to_fill

def make_circle_assignments():
    """Assigns each team to the games they play"""
    teams = NUM_TEAMS
    
    circle = list(range(1, teams + 1))

    ## Get an even number of teams. If odd, treat last one as bye
    if ODD:
        teams += 1
        circle = ["BYE"] + circle

    assignments = []
    for week in range(teams - 1):
        top = circle[: teams // 2]
        bottom = circle[teams // 2 :]
        bottom.reverse()
        
        pairs = list(zip(top, bottom))

        ## This is necessary to have team 1 have even split of red and yellow, if even
        if week % 2 == 1 and not ODD:
            pairs[0] = tuple_swap(pairs[0])

        assignments.append(pairs)
        
        circle = circle[:1] + circle[teams - 1:] + circle[1:teams - 1]

    return assignments

def main():

    if not ODD and NUM_TEAMS > 12:
        print("Sorry, this program does not support an even number of teams greater than 12.")
        return
    
    if NUM_TEAMS == 12:
        assignments = get_12()

    else:
        assignments = make_circle_assignments()

        if ODD:
            # Move BYEs to back
            assignments = [week[1:] + [week[0]] for week in assignments]
        elif NUM_TEAMS > 4:
            # If even, need to use constraint satisfaction to solve
            shuffle_sheets(assignments)
            assignments = assign_sheets_CSP(assignments)

    if SHUFFLE_WEEKS:
        random.shuffle(assignments)

    analyze(assignments)
    print()

    print("week,", end='')
    header_list  =  ["sheet" + str(i) for i in range(1, len(assignments[0]) + 1)]
    if ODD:
        header_list[-1] = "BYE"
    print(','.join(header_list))

    for week,games in enumerate(assignments):
        print(week + 1, games)


if __name__ == "__main__":
    main()
