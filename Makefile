# Makefile for PCG Documentation
# Alternative to npm commands for those who prefer Make

.PHONY: help setup serve build clean test

# Default target - show help
help:
	@echo "PCG Documentation Build System"
	@echo ""
	@echo "Available commands:"
	@echo "  make setup  - Install all dependencies (mdbook, npm packages)"
	@echo "  make serve  - Start development server with auto-reload"
	@echo "  make build  - Build production site"
	@echo "  make clean  - Remove generated files and dependencies"
	@echo "  make test   - Run build to verify everything works"
	@echo ""

# Install all dependencies
setup:
	npm run setup

# Start development server
serve:
	npm run serve

# Build for production
build:
	npm run build

# Clean generated files
clean:
	npm run clean

# Test that build works
test:
	npm run test
