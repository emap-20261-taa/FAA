#!/bin/bash

# Exit on any error
set -e

echo "Setting up Lean 4 development environment..."

# Install Lean 4
echo "Installing Lean 4..."
curl -L https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:stable

# Add elan to PATH permanently for this session
export PATH="$HOME/.elan/bin:$PATH"
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc

# Verify Lean installation
echo "Verifying Lean installation..."
lean --version

# Build the project
echo "Building the project..."
lake build

echo "Setup complete! Your Lean 4 development environment is ready."
echo "You can now open main.lean to start coding." 