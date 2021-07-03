/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.voila

import java.nio.file.Path

import viper.silver

class TestAnnotationParser extends silver.testing.TestAnnotationParser {
  def parse(file: Path)
           : (List[silver.testing.TestAnnotationParseError],
              List[silver.testing.TestAnnotation]) =

    parseAnnotations(file)
}
