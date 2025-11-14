def vacuum_world():
    goal_state = {'A': '0', 'B': '0'}
    cost = 0

    location_input = input("Enter Location of Vacuum (A or B): ")
    status_input = input(f"Enter status of {location_input} (1=Dirty, 0=Clean): ")
    status_input_complement = input("Enter status of the other room (1=Dirty, 0=Clean): ")

    print("Initial Location Condition:", goal_state)

    if location_input == 'A':
        print("Vacuum is placed in Location A")

        if status_input == '1':
            print("Location A is Dirty.")
            # Suck the dirt and mark it as clean
            goal_state['A'] = '0'
            cost += 1  # cost for cleaning
            print("Cost for CLEANING A:", cost)
            print("Location A has been Cleaned.")

            if status_input_complement == '1':
                print("Location B is Dirty.")
                print("Moving right to the Location B.")
                cost += 1  # cost for moving right
                print("COST for moving RIGHT:", cost)
                goal_state['B'] = '0'
                cost += 1  
                print("COST for SUCK:", cost)
                print("Location B has been Cleaned.")
            else:
                print("Location B is already clean.")
                print("No action. Cost:", cost)

        elif status_input == '0':
            print("Location A is already clean.")

            if status_input_complement == '1':
                print("Location B is Dirty.")
                print("Moving RIGHT to the Location B.")
                cost += 1  # cost for moving right
                print("COST for moving RIGHT:", cost)
                goal_state['B'] = '0'
                cost += 1  # cost for cleaning
                print("Cost for SUCK:", cost)
                print("Location B has been Cleaned.")
            else:
                print("Location B is already clean.")
                print("No action. Cost:", cost)

    else:  
        print("Vacuum is placed in Location B")

        if status_input == '1':
            print("Location B is Dirty.")
            goal_state['B'] = '0'
            cost += 1  # cost for cleaning
            print("COST for CLEANING:", cost)
            print("Location B has been Cleaned.")

            if status_input_complement == '1':
                print("Location A is Dirty.")
                print("Moving LEFT to the Location A.")
                cost += 1  # cost for moving left
                print("COST for moving LEFT:", cost)
                goal_state['A'] = '0'
                cost += 1  # cost for cleaning
                print("COST for SUCK:", cost)
                print("Location A has been Cleaned.")
            else:
                print("Location A is already clean.")
                print("No action. Cost:", cost)

        elif status_input == '0':
            print("Location B is already clean.")

            if status_input_complement == '1':
                print("Location A is Dirty.")
                print("Moving LEFT to the Location A.")
                cost += 1  # cost for moving left
                print("COST for moving LEFT:", cost)
                goal_state['A'] = '0'
                cost += 1  # cost for cleaning
                print("Cost for SUCK:", cost)
                print("Location A has been Cleaned.")
            else:
                print("Location A is already clean.")
                print("No action. Cost:", cost)

    print("GOAL STATE:")
    print(goal_state)
    print("Performance Measurement (Cost):", cost)

vacuum_world()
