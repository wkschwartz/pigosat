// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import "testing"
import "regexp"

var semanticVersionTests = []SemanticVersion{
	Version, // Test PiGoSAT's actual version
	{0, 1, 0, "b", 0},
	{1, 2, 3, "", 1}}
var semanticVersionRE = regexp.MustCompile(`\d+\.\d+\.\d+(?:\.?[abc]\.?\d+)?`)

func TestSemanticVersionString(t *testing.T) {
	for _, v := range semanticVersionTests {
		if s := v.String(); !semanticVersionRE.MatchString(s) {
			t.Errorf("Bad version string: %s", s)
		}
	}
}
