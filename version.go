// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import "fmt"

// Struct SemanticVersion implements an immutable semantic version.
type SemanticVersion struct {
	major, minor, patch uint
	// "a" for alpha, "b" for beta, "c" for release candidate, "" for stable
	prerelease string
	// Ignored if not a prerelease
	step uint
}

func (v SemanticVersion) Major() uint        { return v.major }
func (v SemanticVersion) Minor() uint        { return v.minor }
func (v SemanticVersion) Patch() uint        { return v.patch }
func (v SemanticVersion) Prerelease() string { return v.prerelease }
func (v SemanticVersion) Step() uint         { return v.step }
func (v SemanticVersion) IsStable() bool     { return v.prerelease == "" }

func (v SemanticVersion) String() string {
	var prerelease string
	if !v.IsStable() {
		prerelease = fmt.Sprintf("%s%d", v.Prerelease(), v.Step())
	}
	return fmt.Sprintf("%d.%d.%d", v.Major(), v.Minor(), v.Patch()) + prerelease
}
