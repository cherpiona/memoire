import re
import six


def _canonical_string_encoder(string):
    """
  <Purpose>
    Encode 'string' to canonical string format.

  <Arguments>
    string:
      The string to encode.

  <Exceptions>
    None.

  <Side Effects>
    None.

  <Returns>
    A string with the canonical-encoded 'string' embedded.
  """
    string = '"%s"' % re.sub(r'(["\\])', r"\\\1", string)
    return string


def _encode_canonical(object, output_function):
    # Helper for encode_canonical.  Older versions of json.encoder don't
    # even let us replace the separators.

    if isinstance(object, six.string_types):
        output_function(_canonical_string_encoder(object))
    elif object is True:
        output_function("true")
    elif object is False:
        output_function("false")
    #  elif object is None:
    #    output_function("null")
    elif isinstance(object, six.integer_types):
        output_function(str(object))
    elif isinstance(object, (tuple, list)):
        output_function("[")
        if len(object):
            for item in object[:-1]:
                _encode_canonical(item, output_function)
                output_function(",")
            _encode_canonical(object[-1], output_function)
        output_function("]")
    elif isinstance(object, dict):
        output_function("{")
        if len(object):
            items = sorted(six.iteritems(object))
            for key, value in items[:-1]:
                output_function(_canonical_string_encoder(key))
                output_function(":")
                _encode_canonical(value, output_function)
                output_function(",")
            key, value = items[-1]
            output_function(_canonical_string_encoder(key))
            output_function(":")
            _encode_canonical(value, output_function)
        output_function("}")
    else:
        raise ValueError("I cannot encode " + repr(object))


def dumps(object):
    """
  <Purpose>
    Encode 'object' in canonical JSON form, as specified at
    http://wiki.laptop.org/go/Canonical_JSON .  It's a restricted
    dialect of JSON in which keys are always lexically sorted,
    there is no whitespace, floats aren't allowed, and only quote
    and backslash get escaped.  The result is encoded in UTF-8,
    and the resulting bits are passed to output_function (if provided),
    or joined into a string and returned.

    Note: This function should be called prior to computing the hash or
    signature of a JSON object in securesystemslib.  For example, generating a
    signature of a signing role object such as 'ROOT_SCHEMA' is required to
    ensure repeatable hashes are generated across different json module
    versions and platforms.  Code elsewhere is free to dump JSON objects in any
    format they wish (e.g., utilizing indentation and single quotes around
    object keys).  These objects are only required to be in "canonical JSON"
    format when their hashes or signatures are needed.

    >>> dumps("")
    '""'
    >>> dumps([1, 2, 3])
    '[1,2,3]'
    >>> dumps([])
    '[]'
    >>> dumps({"A": [99]})
    '{"A":[99]}'
    >>> dumps({"x" : 3, "y" : 2})
    '{"x":3,"y":2}'

  <Arguments>
    object:
      The object to be encoded.

  <Exceptions>
    ValueError, if 'object' cannot be encoded

  <Returns>
    A 'bytes' object representing the 'object' encoded in canonical JSON form.
  """
    result = []
    _encode_canonical(object, result.append)
    return "".join(result).encode("utf8")
